open Error

type scalar = Local of int | Const of int64
type expression = Value of scalar | Add of scalar * scalar
type value = Scalar of scalar | Closure of value list * Erase.term
type state = { next : int; bindings : (int * expression) list }

(* A compiler portability limit, counting parameters and generated locals. *)
let max_locals = 50_000
let max_parameters = 1_000
let limit_error count kind =
  Backend ("function exceeds " ^ string_of_int count ^ " " ^ kind)
let local_limit = limit_error max_locals "parameters and locals"
let parameter_limit = limit_error max_parameters "parameters"

let as_scalar = function
  | Scalar s -> Ok s
  | Closure _ -> Error (Backend "function used as a scalar")

(* Static closure expansion is deliberately limited to this pure, finite slice.
   Arithmetic stays executable. Every expanded addition gets a Wasm local. *)
let rec evaluate budget state scope term =
  let* () = Budget.tick budget in
  match term with
  | Erase.Local k ->
      let* value = Option.to_result ~none:(Invalid_index k) (List.nth_opt scope k) in
      Ok (value, state)
  | Erase.Const n -> Ok (Scalar (Const n), state)
  | Erase.Add (a, b) ->
      let* a, state = evaluate budget state scope a in
      let* a = as_scalar a in
      let* b, state = evaluate budget state scope b in
      let* b = as_scalar b in
      let* () = if state.next >= max_locals then Error local_limit else Ok () in
      let local = state.next in
      let state = { next = local + 1; bindings = (local, Add (a, b)) :: state.bindings } in
      Ok (Scalar (Local local), state)
  | Erase.Fn body -> Ok (Closure (scope, body), state)
  | Erase.Call (f, a) ->
      let* f, state = evaluate budget state scope f in
      let* a, state = evaluate budget state scope a in
      apply budget state f a
  | Erase.Let (a, body) ->
      let* a, state = evaluate budget state scope a in
      evaluate budget state (a :: scope) body
and apply budget state f a =
  let* () = Budget.tick budget in
  match f with
  | Scalar _ -> Error Expected_function
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

let emit_expression output = function
  | Value s -> emit_scalar output s
  | Add (a, b) -> emit_scalar output a; emit_scalar output b; byte output 0x6a

let emit budget program =
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
  let* () = List.fold_left (fun acc (index, expression) ->
    let* () = acc in
    let* () = Budget.tick budget in
    emit_expression code expression;
    byte code 0x21;
    unsigned code index;
    Ok ()) (Ok ()) (List.rev state.bindings) in
  emit_expression code (Value result);
  byte code 0x0b;
  section output 10 (contents (fun b ->
    unsigned b 1; unsigned b (Buffer.length code); Buffer.add_buffer b code));
  Ok (Buffer.contents output)
