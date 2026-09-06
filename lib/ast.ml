type relevance = Runtime | Erased

type comparison = Equal | Less | Less_equal

type ty = U32 | Bool | Eq of term * term | Pi of relevance * ty * ty
and term =
  | Var of int
  | Lit of int64
  | Boolean of bool
  | Compare of comparison * term * term
  | If of term * term * term
  | Add of term * term
  | Lam of relevance * ty * term
  | App of relevance * term * term
  | Let of relevance * ty * term * term
  | Refl of term
  | Ann of term * ty

let mask = 0xffff_ffffL
let add a b = Int64.logand (Int64.add a b) mask
let compare op a b = match op with
  | Equal -> a = b
  | Less -> a < b
  | Less_equal -> a <= b

open Error

(* Binder depth includes indices inside types. Substitution shares the budget. *)
let rec map_term budget variable depth term =
  let* () = Budget.tick budget in
  match term with
  | Var k -> variable depth k
  | Lit n -> Ok (Lit n)
  | Boolean b -> Ok (Boolean b)
  | Compare (op, a, b) ->
      let* a = map_term budget variable depth a in
      let* b = map_term budget variable depth b in
      Ok (Compare (op, a, b))
  | If (c, a, b) ->
      let* c = map_term budget variable depth c in
      let* a = map_term budget variable depth a in
      let* b = map_term budget variable depth b in
      Ok (If (c, a, b))
  | Add (a, b) ->
      let* a = map_term budget variable depth a in
      let* b = map_term budget variable depth b in
      Ok (Add (a, b))
  | Lam (r, a, body) ->
      let* a = map_ty budget variable depth a in
      let* body = map_term budget variable (depth + 1) body in
      Ok (Lam (r, a, body))
  | App (r, f, a) ->
      let* f = map_term budget variable depth f in
      let* a = map_term budget variable depth a in
      Ok (App (r, f, a))
  | Let (r, a, value, body) ->
      let* a = map_ty budget variable depth a in
      let* value = map_term budget variable depth value in
      let* body = map_term budget variable (depth + 1) body in
      Ok (Let (r, a, value, body))
  | Refl a -> Result.map (fun a -> Refl a) (map_term budget variable depth a)
  | Ann (a, ty) ->
      let* a = map_term budget variable depth a in
      let* ty = map_ty budget variable depth ty in
      Ok (Ann (a, ty))
and map_ty budget variable depth ty =
  let* () = Budget.tick budget in
  match ty with
  | U32 -> Ok U32
  | Bool -> Ok Bool
  | Eq (a, b) ->
      let* a = map_term budget variable depth a in
      let* b = map_term budget variable depth b in
      Ok (Eq (a, b))
  | Pi (r, a, b) ->
      let* a = map_ty budget variable depth a in
      let* b = map_ty budget variable (depth + 1) b in
      Ok (Pi (r, a, b))

let shift_variable delta depth k =
  match () with
  | () when k < 0 -> Error (Invalid_index k)
  | () when k < depth -> Ok (Var k)
  | () when k + delta < depth -> Error (Invalid_index (k + delta))
  | () -> Ok (Var (k + delta))

let shift_term b delta t = map_term b (shift_variable delta) 0 t
let shift_ty b delta t = map_ty b (shift_variable delta) 0 t

(* Remove the substituted binder and lift the replacement under local binders. *)
let substitute_variable budget replacement depth k =
  match () with
  | () when k < 0 -> Error (Invalid_index k)
  | () when k = depth -> shift_term budget depth replacement
  | () -> Ok (Var (if k > depth then k - 1 else k))

let subst_term b value body = map_term b (substitute_variable b value) 0 body
let subst_ty b value body = map_ty b (substitute_variable b value) 0 body
