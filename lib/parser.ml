open Error
open Ast

type sexp = Atom of string | List of sexp list
type token = Left | Right | Word of string

let tokenize source =
  let word = Buffer.create 32 in
  let flush acc =
    if Buffer.length word = 0 then acc
    else let s = Buffer.contents word in Buffer.clear word; Word s :: acc
  in
  let step (comment, acc) c =
    if comment then (c <> '\n', acc)
    else match c with
    | ' ' | '\n' | '\r' | '\t' -> (false, flush acc)
    | ';' -> (true, flush acc)
    | '(' -> (false, Left :: flush acc)
    | ')' -> (false, Right :: flush acc)
    | _ -> Buffer.add_char word c; (false, acc)
  in
  let _, acc = String.fold_left step (false, []) source in
  List.rev (flush acc)

let sexp budget source =
  let rec one depth tokens =
    let* () = Budget.tick budget in
    if depth > 128 then Error (Parse "nesting exceeds 128")
    else match tokens with
    | [] -> Error (Parse "unexpected end of input")
    | Right :: _ -> Error (Parse "unexpected closing parenthesis")
    | Word s :: rest -> Ok (Atom s, rest)
    | Left :: rest -> many (depth + 1) [] rest
  and many depth acc = function
    | [] -> Error (Parse "unclosed parenthesis")
    | Right :: rest -> Ok (List (List.rev acc), rest)
    | (Left :: _ | Word _ :: _) as tokens ->
        let* item, rest = one depth tokens in
        many depth (item :: acc) rest
  in
  if String.length source > 1_048_576 then Error (Parse "source exceeds 1 MiB")
  else
    let* tree, rest = one 0 (tokenize source) in
    match rest with [] -> Ok tree | _ :: _ -> Error (Parse "expected one export")

let relevance = function
  | Atom "run" -> Ok Runtime
  | Atom "erase" -> Ok Erased
  | Atom _ | List _ -> Error (Parse "expected run or erase")

let lookup name names =
  let rec loop i = function
    | [] -> Error (Unknown_name name)
    | x :: rest -> if x = name then Ok (Var i) else loop (i + 1) rest
  in loop 0 names

let rec ty budget names tree =
  let* () = Budget.tick budget in
  match tree with
  | Atom "u32" -> Ok U32
  | List [Atom "eq"; a; b] ->
      let* a = term budget names a in
      let* b = term budget names b in
      Ok (Eq (a, b))
  | List [Atom "pi"; List [r; Atom name; a]; b] ->
      let* r = relevance r in
      let* a = ty budget names a in
      let* b = ty budget (name :: names) b in
      Ok (Pi (r, a, b))
  | Atom _ | List _ -> Error (Parse "expected u32, eq, or pi type")
and term budget names tree =
  let* () = Budget.tick budget in
  match tree with
  | Atom name ->
      Option.fold
        ~none:(fun () -> lookup name names)
        ~some:(fun n () -> if n < 0L || n > mask then Error (Invalid_u32 n) else Ok (Lit n))
        (Int64.of_string_opt name) ()
  | List [Atom "add"; a; b] ->
      let* a = term budget names a in
      let* b = term budget names b in
      Ok (Add (a, b))
  | List [Atom "fn"; List [r; Atom name; a]; body] ->
      let* r = relevance r in
      let* a = ty budget names a in
      let* body = term budget (name :: names) body in
      Ok (Lam (r, a, body))
  | List [Atom "app"; r; f; a] ->
      let* r = relevance r in
      let* f = term budget names f in
      let* a = term budget names a in
      Ok (App (r, f, a))
  | List [Atom "let"; List [r; Atom name; a]; value; body] ->
      let* r = relevance r in
      let* a = ty budget names a in
      let* value = term budget names value in
      let* body = term budget (name :: names) body in
      Ok (Let (r, a, value, body))
  | List [Atom "refl"; a] -> Result.map (fun a -> Refl a) (term budget names a)
  | List [Atom "ann"; a; t] ->
      let* a = term budget names a in
      let* t = ty budget names t in
      Ok (Ann (a, t))
  | List _ -> Error (Parse "invalid term form")

let parse budget source =
  let* tree = sexp budget source in
  match tree with
  | List [Atom "export"; Atom "main"; body] -> term budget [] body
  | Atom _ | List _ -> Error (Parse "expected (export main TERM)")
