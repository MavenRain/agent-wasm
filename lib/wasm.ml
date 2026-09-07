open Error

type scalar = Local of int | Const of int64
type expression =
  | Value of scalar
  | Add of scalar * scalar
  | Compare of Erase.comparison * scalar * scalar
  | If of scalar * branch * branch
and branch = { bindings : (int * expression) list; result : scalar }
type value =
  | Scalar of scalar
  | Closure of value list * Erase.term
  | Pair of value * value
  | Record of (string * value) list
type state = { next : int; bindings : (int * expression) list }

(* A compiler portability limit, counting parameters and generated locals. *)
let max_locals = 50_000
let max_parameters = 1_000
let limit_error count kind =
  Backend ("function exceeds " ^ string_of_int count ^ " " ^ kind)
let local_limit = limit_error max_locals "parameters and locals"
let parameter_limit = limit_error max_parameters "parameters"

let bind state expression =
  let* () = if state.next >= max_locals then Error local_limit else Ok () in
  let local = state.next in
  let state = { next = local + 1; bindings = (local, expression) :: state.bindings } in
  Ok (Scalar (Local local), state)

let as_scalar = function
  | Scalar s -> Ok s
  | Closure _ -> Error (Backend "function used as a scalar")
  | Pair _ -> Error (Backend "pair used as a scalar")
  | Record _ -> Error (Backend "record used as a scalar")

(* Branch effects run once before field selection. Unselected branch locals
   are never read by the selected arm. Products and records have no heap representation. *)
let rec merge budget state condition a b =
  let* () = Budget.tick budget in
  match a, b with
  | Scalar a, Scalar b ->
      bind state (If (condition, { bindings = []; result = a },
                                { bindings = []; result = b }))
  | Pair (a1, a2), Pair (b1, b2) ->
      let* first, state = merge budget state condition a1 b1 in
      let* second, state = merge budget state condition a2 b2 in
      Ok (Pair (first, second), state)
  | Record a, Record b ->
      let* fields, state = merge_fields budget state condition a b in
      Ok (Record fields, state)
  | Closure _, _ | (Scalar _ | Pair _ | Record _), Closure _ ->
      Error (Backend "conditional function value")
  | Scalar _, (Pair _ | Record _) | Pair _, (Scalar _ | Record _)
  | Record _, (Scalar _ | Pair _) ->
      Error (Backend "conditional shape mismatch")
and merge_fields budget state condition a b =
  let* () = Budget.tick budget in
  match a, b with
  | [], [] -> Ok ([], state)
  | (label, a) :: rest_a, (other_label, b) :: rest_b ->
      if label <> other_label then Error (Backend "conditional record label mismatch")
      else
        let* value, state = merge budget state condition a b in
        let* rest, state = merge_fields budget state condition rest_a rest_b in
        Ok ((label, value) :: rest, state)
  | [], _ :: _ | _ :: _, [] -> Error (Backend "conditional record length mismatch")

let rec field budget label fields =
  let* () = Budget.tick budget in
  match fields with
  | [] -> Error (Backend ("unknown record field: " ^ label))
  | (candidate, value) :: rest ->
      if candidate = label then Ok value else field budget label rest

(* Static closure expansion is deliberately limited to this pure, finite slice.
   Scalar operations stay executable and each receives a Wasm local. *)
let rec evaluate budget state scope term =
  let* () = Budget.tick budget in
  match term with
  | Erase.Local k ->
      if k < 0 then Error (Invalid_index k)
      else
        let* value = Option.to_result ~none:(Invalid_index k) (List.nth_opt scope k) in
        Ok (value, state)
  | Erase.Const n ->
      if n < 0L || n > 0xffff_ffffL then Error (Invalid_u32 n)
      else Ok (Scalar (Const n), state)
  | Erase.Pair (a, b) ->
      let* a, state = evaluate budget state scope a in
      let* b, state = evaluate budget state scope b in
      Ok (Pair (a, b), state)
  | Erase.Record fields ->
      let* fields, state = evaluate_fields budget state scope fields in
      Ok (Record fields, state)
  | Erase.Field (value, label) ->
      let* value, state = evaluate budget state scope value in
      (match value with
       | Record fields ->
           let* value = field budget label fields in
           Ok (value, state)
       | Scalar _ | Pair _ | Closure _ -> Error (Backend "field projection of non-record"))
  | Erase.Fst a ->
      let* a, state = evaluate budget state scope a in
      (match a with
       | Pair (a, _) -> Ok (a, state)
       | Scalar _ | Closure _ | Record _ -> Error (Backend "projection of non-pair"))
  | Erase.Snd a ->
      let* a, state = evaluate budget state scope a in
      (match a with
       | Pair (_, b) -> Ok (b, state)
       | Scalar _ | Closure _ | Record _ -> Error (Backend "projection of non-pair"))
  | Erase.Add (a, b) ->
      let* a, state = evaluate budget state scope a in
      let* a = as_scalar a in
      let* b, state = evaluate budget state scope b in
      let* b = as_scalar b in
      bind state (Add (a, b))
  | Erase.Compare (op, a, b) ->
      let* a, state = evaluate budget state scope a in
      let* a = as_scalar a in
      let* b, state = evaluate budget state scope b in
      let* b = as_scalar b in
      bind state (Compare (op, a, b))
  | Erase.If (c, a, b) ->
      let* c, state = evaluate budget state scope c in
      let* c = as_scalar c in
      (* Branch instructions remain nested, while local numbers are disjoint. *)
      let* a, a_state = evaluate budget { next = state.next; bindings = [] } scope a in
      let* b, b_state = evaluate budget { next = a_state.next; bindings = [] } scope b in
      (match a, b with
       | Scalar a, Scalar b ->
           bind { state with next = b_state.next }
             (If (c, { bindings = a_state.bindings; result = a },
                     { bindings = b_state.bindings; result = b }))
       | Pair _, Pair _ | Record _, Record _ ->
           let* _, state = bind { state with next = b_state.next }
             (If (c, { bindings = a_state.bindings; result = Const 0L },
                     { bindings = b_state.bindings; result = Const 0L })) in
           merge budget state c a b
       | Closure _, _ | (Scalar _ | Pair _ | Record _), Closure _ ->
           Error (Backend "conditional function value")
       | Scalar _, (Pair _ | Record _) | Pair _, (Scalar _ | Record _)
       | Record _, (Scalar _ | Pair _) ->
           Error (Backend "conditional shape mismatch"))
  | Erase.Fn body -> Ok (Closure (scope, body), state)
  | Erase.Call (f, a) ->
      let* f, state = evaluate budget state scope f in
      let* a, state = evaluate budget state scope a in
      apply budget state f a
  | Erase.Let (a, body) ->
      let* a, state = evaluate budget state scope a in
      evaluate budget state (a :: scope) body
and evaluate_fields budget state scope fields =
  let* () = Budget.tick budget in
  match fields with
  | [] -> Ok ([], state)
  | (label, term) :: rest ->
      let* value, state = evaluate budget state scope term in
      let* rest, state = evaluate_fields budget state scope rest in
      Ok ((label, value) :: rest, state)
and apply budget state f a =
  let* () = Budget.tick budget in
  match f with
  | Scalar _ | Pair _ | Record _ -> Error Expected_function
  | Closure (scope, body) -> evaluate budget state (a :: scope) body

let byte = Buffer.add_uint8
let rec unsigned buffer n =
  let low = n land 0x7f in
  let rest = n lsr 7 in
  if rest = 0 then byte buffer low
  else (byte buffer (low lor 0x80); unsigned buffer rest)

let rec signed buffer n =
  let low = Int64.to_int (Int64.logand n 0x7fL) in
  let rest = Int64.shift_right n 7 in
  let done_ = (rest = 0L && low land 0x40 = 0) || (rest = -1L && low land 0x40 <> 0) in
  if done_ then byte buffer low
  else (byte buffer (low lor 0x80); signed buffer rest)

let contents write = let b = Buffer.create 128 in write b; Buffer.contents b
let section output id payload =
  byte output id;
  unsigned output (String.length payload);
  Buffer.add_string output payload

let emit_scalar output = function
  | Local k -> byte output 0x20; unsigned output k
  | Const n ->
      byte output 0x41;
      signed output (if n > 0x7fff_ffffL then Int64.sub n 0x1_0000_0000L else n)

let rec emit_expression budget output = function
  | Value s -> emit_scalar output s; Ok ()
  | Add (a, b) -> emit_scalar output a; emit_scalar output b; byte output 0x6a; Ok ()
  | Compare (op, a, b) ->
      emit_scalar output a; emit_scalar output b;
      byte output (match op with Erase.Equal -> 0x46 | Erase.Less -> 0x49 | Erase.Less_equal -> 0x4d);
      Ok ()
  | If (c, a, b) ->
      emit_scalar output c;
      byte output 0x04; byte output 0x7f;
      let* () = emit_bindings budget output a.bindings in
      emit_scalar output a.result;
      byte output 0x05;
      let* () = emit_bindings budget output b.bindings in
      emit_scalar output b.result;
      byte output 0x0b;
      Ok ()
and emit_bindings budget output bindings =
  List.fold_left (fun acc (index, expression) ->
    let* () = acc in
    let* () = Budget.tick budget in
    let* () = emit_expression budget output expression in
    byte output 0x21;
    unsigned output index;
    Ok ()) (Ok ()) (List.rev bindings)

let emit budget program =
  let* () = if program.Erase.arity < 0 then Error (Backend "negative function arity") else Ok () in
  let* () = if program.Erase.arity > max_parameters then Error parameter_limit else Ok () in
  let state = { next = program.Erase.arity; bindings = [] } in
  let* entry, state = evaluate budget state [] program.body in
  let rec parameters index value state =
    if index = program.arity then
      let* scalar = as_scalar value in
      Ok (scalar, state)
    else
      let* value, state = apply budget state value (Scalar (Local index)) in
      parameters (index + 1) value state
  in
  let* result, state = parameters 0 entry state in
  let output = Buffer.create 256 in
  Buffer.add_string output "\x00asm\x01\x00\x00\x00";
  section output 1 (contents (fun b ->
    unsigned b 1; byte b 0x60; unsigned b program.arity;
    let rec parameter_types remaining =
      if remaining = 0 then ()
      else (byte b 0x7f; parameter_types (remaining - 1))
    in
    parameter_types program.arity;
    unsigned b 1; byte b 0x7f));
  section output 3 "\x01\x00";
  section output 7 "\x01\x04main\x00\x00";
  let code = Buffer.create 128 in
  let local_count = state.next - program.arity in
  if local_count = 0 then unsigned code 0
  else (unsigned code 1; unsigned code local_count; byte code 0x7f);
  let* () = emit_bindings budget code state.bindings in
  let* () = emit_expression budget code (Value result) in
  byte code 0x0b;
  section output 10 (contents (fun b ->
    unsigned b 1; unsigned b (Buffer.length code); Buffer.add_buffer b code));
  Ok (Buffer.contents output)
