open Error
open Ast

type phase = Execute | Ghost
type binding = { relevance : relevance; ty : ty }
type checked = { source : term; parameters : int }
let term c = c.source
let arity c = c.parameters

let literal = function
  | Lit n -> Some n
  | Boolean _ | Compare _ | If _ | Var _ | Add _ | Lam _ | App _ | Let _ | Refl _ | Ann _ -> None

let rec normal budget term =
  let* () = Budget.tick budget in
  match term with
  | Var _ | Lit _ | Boolean _ -> Ok term
  | Compare (op, a, b) ->
      let* a = normal budget a in
      let* b = normal budget b in
      let result = Option.bind (literal a) (fun x -> Option.map (compare op x) (literal b)) in
      Ok (Option.fold ~none:(Compare (op, a, b)) ~some:(fun b -> Boolean b) result)
  | If (c, a, b) ->
      let* c = normal budget c in
      (match c with
       | Boolean true -> normal budget a
       | Boolean false -> normal budget b
       | Var _ | Lit _ | Compare _ | If _ | Add _ | Lam _ | App _ | Let _ | Refl _ | Ann _ ->
           let* a = normal budget a in
           let* b = normal budget b in
           Ok (If (c, a, b)))
  | Add (a, b) ->
      let* a = normal budget a in
      let* b = normal budget b in
      let sum = Option.bind (literal a) (fun x -> Option.map (add x) (literal b)) in
      Ok (Option.fold ~none:(Add (a, b)) ~some:(fun n -> Lit n) sum)
  | Lam (r, a, body) ->
      let* a = normal_ty budget a in
      let* body = normal budget body in
      Ok (Lam (r, a, body))
  | App (r, f, a) ->
      let* f = normal budget f in
      let* a = normal budget a in
      (match f with
       | Lam (_, _, body) -> let* body = subst_term budget a body in normal budget body
       | Boolean _ | Compare _ | If _ | Var _ | Lit _ | Add _ | App _ | Let _ | Refl _ | Ann _ -> Ok (App (r, f, a)))
  | Let (_, _, value, body) ->
      let* value = normal budget value in
      let* body = subst_term budget value body in
      normal budget body
  | Refl a -> Result.map (fun a -> Refl a) (normal budget a)
  | Ann (a, _) -> normal budget a
and normal_ty budget = function
  | U32 -> let* () = Budget.tick budget in Ok U32
  | Bool -> let* () = Budget.tick budget in Ok Bool
  | Eq (a, b) ->
      let* a = normal budget a in
      let* b = normal budget b in
      Ok (Eq (a, b))
  | Pi (r, a, b) ->
      let* a = normal_ty budget a in
      let* b = normal_ty budget b in
      Ok (Pi (r, a, b))

let equivalent budget a b =
  let* a = normal_ty budget a in
  let* b = normal_ty budget b in
  if a = b then Ok () else Error Type_mismatch

let argument_phase phase = function Runtime -> phase | Erased -> Ghost
let domain_allowed relevance ty =
  match relevance with
  | Erased -> Ok ()
  | Runtime -> (match ty with Eq _ -> Error Runtime_proof | U32 | Bool | Pi _ -> Ok ())
let result_allowed phase ty =
  match phase with
  | Ghost -> Ok ty
  | Execute -> (match ty with Eq _ -> Error Runtime_proof | U32 | Bool | Pi _ -> Ok ty)

let rec well_formed budget context ty =
  let* () = Budget.tick budget in
  match ty with
  | U32 | Bool -> Ok ()
  | Eq (a, b) ->
      let* () = check_term budget Ghost context a U32 in
      check_term budget Ghost context b U32
  | Pi (r, a, b) ->
      let* () = well_formed budget context a in
      let* () = domain_allowed r a in
      well_formed budget ({ relevance = r; ty = a } :: context) b
and infer budget phase context term =
  let* () = Budget.tick budget in
  let* ty = match term with
  | Var k ->
      if k < 0 then Error (Invalid_index k)
      else
        let* b = Option.to_result ~none:(Invalid_index k) (List.nth_opt context k) in
        if phase = Execute && b.relevance = Erased then Error (Erased_use k)
        else shift_ty budget (k + 1) b.ty
  | Lit n -> if n < 0L || n > mask then Error (Invalid_u32 n) else Ok U32
  | Boolean _ -> Ok Bool
  | Compare (_, a, b) ->
      let* () = check_term budget phase context a U32 in
      let* () = check_term budget phase context b U32 in
      Ok Bool
  | If (c, a, b) ->
      let* () = check_term budget phase context c Bool in
      let* () = check_term budget phase context a U32 in
      let* () = check_term budget phase context b U32 in
      Ok U32
  | Add (a, b) ->
      let* () = check_term budget phase context a U32 in
      let* () = check_term budget phase context b U32 in
      Ok U32
  | Lam (r, a, body) ->
      let* () = well_formed budget context a in
      let* () = domain_allowed r a in
      let* b = infer budget phase ({ relevance = r; ty = a } :: context) body in
      Ok (Pi (r, a, b))
  | App (r, f, a) ->
      let* fty = infer budget phase context f in
      (match fty with
       | Pi (expected_r, domain, range) ->
           if r <> expected_r then Error Type_mismatch
           else
             let* () = check_term budget (argument_phase phase r) context a domain in
             subst_ty budget a range
       | U32 | Bool | Eq _ -> Error Expected_function)
  | Let (r, a, value, body) ->
      let* () = well_formed budget context a in
      let* () = check_term budget (argument_phase phase r) context value a in
      let* b = infer budget phase ({ relevance = r; ty = a } :: context) body in
      subst_ty budget value b
  | Refl a ->
      let* () = check_term budget Ghost context a U32 in
      Ok (Eq (a, a))
  | Ann (a, ty) ->
      let* () = well_formed budget context ty in
      let* () = check_term budget phase context a ty in
      Ok ty
  in result_allowed phase ty
and check_term budget phase context term expected =
  let* actual = infer budget phase context term in
  equivalent budget actual expected

let check budget source =
  let* ty = infer budget Execute [] source in
  let rec export_arity count = function
    | U32 -> Ok count
    | Pi (Runtime, U32, rest) -> export_arity (count + 1) rest
    | Bool | Eq _ | Pi (Erased, _, _) | Pi (Runtime, (Bool | Eq _ | Pi _), _) -> Error Unsupported_export
  in
  let* parameters = export_arity 0 ty in
  Ok { source; parameters }
