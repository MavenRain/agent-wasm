open Error

type comparison = Equal | Less | Less_equal

type term =
  | Local of int
  | Const of int64
  | Add of term * term
  | Pair of term * term
  | Fst of term
  | Snd of term
  | Record of (string * term) list
  | Field of term * string
  | Compare of comparison * term * term
  | If of term * term * term
  | Fn of term
  | Call of term * term
  | Let of term * term

type t = { body : term; arity : int }

let program arity body = { body; arity }

let run budget checked =
  (* Only the finite scalar shape survives, never source types or evidence. *)
  let rec zero ty =
    let* () = Budget.tick budget in
    match ty with
    | Ast.U32 | Ast.Bool -> Ok (Const 0L)
    | Ast.Product (a, b) ->
        let* a = zero a in
        let* b = zero b in
        Ok (Pair (a, b))
    | Ast.Record fields -> Result.map (fun fields -> Record fields) (zero_fields fields)
    | Ast.Sum (a, b) ->
        let* a = zero a in
        let* b = zero b in
        Ok (Pair (Const 1L, Pair (a, b)))
    | Ast.Refine (a, _) -> zero a
    | Ast.Eq _ | Ast.Pi _ -> Error (Backend "unsupported zero-fill payload")
  and zero_fields fields =
    let* () = Budget.tick budget in
    match fields with
    | [] -> Ok []
    | (label, ty) :: rest ->
        let* value = zero ty in
        let* rest = zero_fields rest in
        Ok ((label, value) :: rest)
  in
  let rec walk scope depth term =
    let* () = Budget.tick budget in
    match term with
    | Ast.Var k ->
        let* level = Option.to_result ~none:(Invalid_index k) (List.nth_opt scope k) in
        let* level = Option.to_result ~none:(Erased_use k) level in
        Ok (Local (depth - level - 1))
    | Ast.Lit n -> Ok (Const n)
    | Ast.Boolean b -> Ok (Const (if b then 1L else 0L))
    | Ast.Inl (other, value) ->
        let* value = walk scope depth value in
        let* other = zero other in
        Ok (Pair (Const 1L, Pair (value, other)))
    | Ast.Inr (other, value) ->
        let* value = walk scope depth value in
        let* other = zero other in
        Ok (Pair (Const 0L, Pair (other, value)))
    | Ast.Case (_, value, a, b) ->
        let* value = walk scope depth value in
        (* The scrutinee gets a runtime-only binder, then each payload gets
           its source binder. Outer levels must account for both. *)
        let* a = walk (Some (depth + 1) :: scope) (depth + 2) a in
        let* b = walk (Some (depth + 1) :: scope) (depth + 2) b in
        Ok (Let (value, If (Fst (Local 0),
          Let (Fst (Snd (Local 0)), a), Let (Snd (Snd (Local 0)), b))))
    | Ast.Pair (a, b) ->
        let* a = walk scope depth a in
        let* b = walk scope depth b in
        Ok (Pair (a, b))
    | Ast.Fst a -> Result.map (fun a -> Fst a) (walk scope depth a)
    | Ast.Snd a -> Result.map (fun a -> Snd a) (walk scope depth a)
    | Ast.RecordValue fields ->
        Result.map (fun fields -> Record fields) (walk_fields scope depth fields)
    | Ast.Field (value, label) ->
        Result.map (fun value -> Field (value, label)) (walk scope depth value)
    | Ast.Pack (_, value, _) | Ast.Value value -> walk scope depth value
    | Ast.Evidence _ -> Error Runtime_proof
    | Ast.Compare (op, a, b) ->
        let op = match op with Ast.Equal -> Equal | Ast.Less -> Less | Ast.Less_equal -> Less_equal in
        let* a = walk scope depth a in
        let* b = walk scope depth b in
        Ok (Compare (op, a, b))
    | Ast.IfProof (_, c, a, b) ->
        let* c = walk scope depth c in
        let* a = walk (None :: scope) depth a in
        let* b = walk (None :: scope) depth b in
        Ok (If (c, a, b))
    | Ast.If (c, a, b) ->
        let* c = walk scope depth c in
        let* a = walk scope depth a in
        let* b = walk scope depth b in
        Ok (If (c, a, b))
    | Ast.Add (a, b) ->
        let* a = walk scope depth a in
        let* b = walk scope depth b in
        Ok (Add (a, b))
    | Ast.Lam (Ast.Erased, _, body) -> walk (None :: scope) depth body
    | Ast.Lam (Ast.Runtime, _, body) ->
        Result.map (fun body -> Fn body) (walk (Some depth :: scope) (depth + 1) body)
    | Ast.App (Ast.Erased, f, _) -> walk scope depth f
    | Ast.App (Ast.Runtime, f, a) ->
        let* f = walk scope depth f in
        let* a = walk scope depth a in
        Ok (Call (f, a))
    | Ast.Let (Ast.Erased, _, _, body) -> walk (None :: scope) depth body
    | Ast.Let (Ast.Runtime, _, value, body) ->
        let* value = walk scope depth value in
        let* body = walk (Some depth :: scope) (depth + 1) body in
        Ok (Let (value, body))
    | Ast.Refl _ -> Error Runtime_proof
    | Ast.Transport (_, _, _, _, value) -> walk scope depth value
    | Ast.Ann (a, _) -> walk scope depth a
  and walk_fields scope depth fields =
    let* () = Budget.tick budget in
    match fields with
    | [] -> Ok []
    | (label, value) :: rest ->
        let* value = walk scope depth value in
        let* rest = walk_fields scope depth rest in
        Ok ((label, value) :: rest)
  in
  let* body = walk [] 0 (Kernel.term checked) in
  Ok { body; arity = Kernel.arity checked }

let dump program =
  let rec term = function
    | Local n -> "v" ^ string_of_int n
    | Const n -> Int64.to_string n
    | Add (a, b) -> "(add " ^ term a ^ " " ^ term b ^ ")"
    | Pair (a, b) -> "(pair " ^ term a ^ " " ^ term b ^ ")"
    | Fst a -> "(fst " ^ term a ^ ")"
    | Snd a -> "(snd " ^ term a ^ ")"
    | Record fields ->
        "(record " ^ String.concat " "
          (List.map (fun (label, value) -> "(" ^ label ^ " " ^ term value ^ ")") fields) ^ ")"
    | Field (value, label) -> "(field " ^ term value ^ " " ^ label ^ ")"
    | Compare (op, a, b) ->
        let name = match op with Equal -> "u32-eq" | Less -> "u32-lt" | Less_equal -> "u32-le" in
        "(" ^ name ^ " " ^ term a ^ " " ^ term b ^ ")"
    | If (c, a, b) -> "(if " ^ term c ^ " " ^ term a ^ " " ^ term b ^ ")"
    | Fn body -> "(fn " ^ term body ^ ")"
    | Call (f, a) -> "(call " ^ term f ^ " " ^ term a ^ ")"
    | Let (a, body) -> "(let " ^ term a ^ " " ^ term body ^ ")"
  in "(export main " ^ term program.body ^ ")\n"
