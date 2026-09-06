open Error

type term =
  | Local of int
  | Const of int64
  | Add of term * term
  | Fn of term
  | Call of term * term
  | Let of term * term

type t = { body : term; arity : int }

let run budget checked =
  let rec walk scope depth term =
    let* () = Budget.tick budget in
    match term with
    | Ast.Var k ->
        let* level = Option.to_result ~none:(Invalid_index k) (List.nth_opt scope k) in
        let* level = Option.to_result ~none:(Erased_use k) level in
        Ok (Local (depth - level - 1))
    | Ast.Lit n -> Ok (Const n)
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
    | Ast.Ann (a, _) -> walk scope depth a
  in
  let* body = walk [] 0 (Kernel.term checked) in
  Ok { body; arity = Kernel.arity checked }

let dump program =
  let rec term = function
    | Local n -> "v" ^ string_of_int n
    | Const n -> Int64.to_string n
    | Add (a, b) -> "(add " ^ term a ^ " " ^ term b ^ ")"
    | Fn body -> "(fn " ^ term body ^ ")"
    | Call (f, a) -> "(call " ^ term f ^ " " ^ term a ^ ")"
    | Let (a, body) -> "(let " ^ term a ^ " " ^ term body ^ ")"
  in "(export main " ^ term program.body ^ ")\n"
