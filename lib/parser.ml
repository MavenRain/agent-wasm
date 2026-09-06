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

let digit c = c >= '0' && c <= '9'
let numeric_name name =
  Option.fold ~none:false
    ~some:(fun (c, _) -> digit c || c = '+' || c = '-')
    (Seq.uncons (String.to_seq name))

let binder name =
  if numeric_name name || name = "true" || name = "false" then Error (Parse "binder name is reserved for literals")
  else Ok ()

let atom names name =
  if not (numeric_name name) then lookup name names
  else if not (String.for_all digit name) then
    Error (Parse "expected an unsigned decimal u32 literal")
  else
    (* Accumulate within u32 so even arbitrarily long tokens have a numeric
       diagnostic, without relying on the host's integer literal syntax. *)
    String.fold_left (fun acc c ->
      let* n = acc in
      let next = Int64.add (Int64.mul n 10L)
        (Int64.of_int (Char.code c - Char.code '0')) in
      if next > mask then Error (Parse "decimal literal outside u32 range")
      else Ok next) (Ok 0L) name
    |> Result.map (fun n -> Lit n)

let rec ty budget names tree =
  let* () = Budget.tick budget in
  match tree with
  | Atom "u32" -> Ok U32
  | Atom "bool" -> Ok Bool
  | List [Atom "sum"; a; b] ->
      let* a = ty budget names a in
      let* b = ty budget names b in
      Ok (Sum (a, b))
  | List [Atom "product"; a; b] ->
      let* a = ty budget names a in
      let* b = ty budget names b in
      Ok (Product (a, b))
  | List [Atom "eq"; a; b] ->
      let* a = term budget names a in
      let* b = term budget names b in
      Ok (Eq (a, b))
  | List [Atom "pi"; List [r; Atom name; a]; b] ->
      let* () = binder name in
      let* r = relevance r in
      let* a = ty budget names a in
      let* b = ty budget (name :: names) b in
      Ok (Pi (r, a, b))
  | Atom _ | List _ -> Error (Parse "expected u32, bool, product, sum, eq, or pi type")
and term budget names tree =
  let* () = Budget.tick budget in
  match tree with
  | Atom "true" -> Ok (Boolean true)
  | Atom "false" -> Ok (Boolean false)
  | Atom name ->
      atom names name
  | List [Atom "inl"; other; value] ->
      let* other = ty budget names other in
      let* value = term budget names value in
      Ok (Inl (other, value))
  | List [Atom "inr"; other; value] ->
      let* other = ty budget names other in
      let* value = term budget names value in
      Ok (Inr (other, value))
  | List [Atom "case"; result; value; List [Atom left; a]; List [Atom right; b]] ->
      let* () = binder left in
      let* () = binder right in
      let* result = ty budget names result in
      let* value = term budget names value in
      let* a = term budget (left :: names) a in
      let* b = term budget (right :: names) b in
      Ok (Case (result, value, a, b))
  | List [Atom "pair"; a; b] ->
      let* a = term budget names a in
      let* b = term budget names b in
      Ok (Pair (a, b))
  | List [Atom "fst"; a] -> Result.map (fun a -> Fst a) (term budget names a)
  | List [Atom "snd"; a] -> Result.map (fun a -> Snd a) (term budget names a)
  | List [Atom ("u32-eq" | "u32-lt" | "u32-le" as op); a; b] ->
      let op = if op = "u32-eq" then Equal else if op = "u32-lt" then Less else Less_equal in
      let* a = term budget names a in
      let* b = term budget names b in
      Ok (Compare (op, a, b))
  | List [Atom "if"; c; a; b] ->
      let* c = term budget names c in
      let* a = term budget names a in
      let* b = term budget names b in
      Ok (If (c, a, b))
  | List [Atom "add"; a; b] ->
      let* a = term budget names a in
      let* b = term budget names b in
      Ok (Add (a, b))
  | List [Atom "fn"; List [r; Atom name; a]; body] ->
      let* () = binder name in
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
      let* () = binder name in
      let* r = relevance r in
      let* a = ty budget names a in
      let* value = term budget names value in
      let* body = term budget (name :: names) body in
      Ok (Let (r, a, value, body))
  | List [Atom "refl"; a] -> Result.map (fun a -> Refl a) (term budget names a)
  | List [Atom "transport"; List [Atom name; family]; a; b; proof; value] ->
      let* () = binder name in
      let* family = ty budget (name :: names) family in
      let* a = term budget names a in
      let* b = term budget names b in
      let* proof = term budget names proof in
      let* value = term budget names value in
      Ok (Transport (family, a, b, proof, value))
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
