open Error
open Ast

type phase = Execute | Ghost
type binding = { relevance : relevance; ty : ty }
type checked = { source : term; parameters : int }
let term c = c.source
let arity c = c.parameters

let literal = function
  | Lit n -> Some n
  | Inl _ | Inr _ | Case _ | Pair _ | Fst _ | Snd _ | Boolean _ | Compare _ | If _ | Var _ | Add _ | Lam _ | App _ | Let _ | Refl _ | Transport _ | Ann _ -> None

let rec normal budget term =
  let* () = Budget.tick budget in
  match term with
  | Var _ | Lit _ | Boolean _ -> Ok term
  | Inl (ty, a) ->
      let* ty = normal_ty budget ty in
      let* a = normal budget a in
      Ok (Inl (ty, a))
  | Inr (ty, a) ->
      let* ty = normal_ty budget ty in
      let* a = normal budget a in
      Ok (Inr (ty, a))
  | Case (ty, value, a, b) ->
      let* value = normal budget value in
      (match value with
       | Inl (_, value) -> let* body = subst_term budget value a in normal budget body
       | Inr (_, value) -> let* body = subst_term budget value b in normal budget body
       | Var _ | Lit _ | Boolean _ | Pair _ | Fst _ | Snd _ | Compare _ | If _
       | Add _ | Lam _ | App _ | Let _ | Refl _ | Transport _ | Ann _ | Case _ ->
           let* ty = normal_ty budget ty in
           let* a = normal budget a in
           let* b = normal budget b in
           Ok (Case (ty, value, a, b)))
  | Pair (a, b) ->
      let* a = normal budget a in
      let* b = normal budget b in
      Ok (Pair (a, b))
  | Fst a ->
      let* a = normal budget a in
      (match a with
       | Pair (a, _) -> Ok a
       | Inl _ | Inr _ | Case _ | Var _ | Lit _ | Boolean _ | Fst _ | Snd _ | Compare _ | If _ | Add _ | Lam _ | App _ | Let _ | Refl _ | Transport _ | Ann _ -> Ok (Fst a))
  | Snd a ->
      let* a = normal budget a in
      (match a with
       | Pair (_, b) -> Ok b
       | Inl _ | Inr _ | Case _ | Var _ | Lit _ | Boolean _ | Fst _ | Snd _ | Compare _ | If _ | Add _ | Lam _ | App _ | Let _ | Refl _ | Transport _ | Ann _ -> Ok (Snd a))
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
       | Inl _ | Inr _ | Case _ | Pair _ | Fst _ | Snd _ | Var _ | Lit _ | Compare _ | If _ | Add _ | Lam _ | App _ | Let _ | Refl _ | Transport _ | Ann _ ->
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
       | Inl _ | Inr _ | Case _ | Pair _ | Fst _ | Snd _ | Boolean _ | Compare _ | If _ | Var _ | Lit _ | Add _ | App _ | Let _ | Refl _ | Transport _ | Ann _ -> Ok (App (r, f, a)))
  | Let (_, _, value, body) ->
      let* value = normal budget value in
      let* body = subst_term budget value body in
      normal budget body
  | Refl a -> Result.map (fun a -> Refl a) (normal budget a)
  | Transport (family, a, b, proof, value) ->
      let* proof = normal budget proof in
      (match proof with
       | Refl _ -> normal budget value
       | Var _ | Lit _ | Boolean _ | Inl _ | Inr _ | Case _ | Pair _ | Fst _ | Snd _ | Compare _ | If _
       | Add _ | Lam _ | App _ | Let _ | Transport _ | Ann _ ->
           let* family = normal_ty budget family in
           let* a = normal budget a in
           let* b = normal budget b in
           let* value = normal budget value in
           Ok (Transport (family, a, b, proof, value)))
  | Ann (a, _) -> normal budget a
and normal_ty budget = function
  | Sum (a, b) ->
      let* () = Budget.tick budget in
      let* a = normal_ty budget a in
      let* b = normal_ty budget b in
      Ok (Sum (a, b))
  | U32 -> let* () = Budget.tick budget in Ok U32
  | Bool -> let* () = Budget.tick budget in Ok Bool
  | Product (a, b) ->
      let* () = Budget.tick budget in
      let* a = normal_ty budget a in
      let* b = normal_ty budget b in
      Ok (Product (a, b))
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
let rec branch_type budget ty =
  let* () = Budget.tick budget in
  match ty with
  | U32 | Bool -> Ok ()
  | Product (a, b) | Sum (a, b) -> let* () = branch_type budget a in branch_type budget b
  | Eq _ | Pi _ -> Error Type_mismatch

let rec runtime_type = function
  | Eq _ -> Error Runtime_proof
  | U32 | Bool | Pi _ -> Ok ()
  | Product (a, b) | Sum (a, b) -> let* () = runtime_type a in runtime_type b

let domain_allowed relevance ty =
  match relevance with
  | Erased -> Ok ()
  | Runtime -> runtime_type ty
let result_allowed phase ty =
  match phase with
  | Ghost -> Ok ty
  | Execute -> let* () = runtime_type ty in Ok ty

let rec well_formed budget context ty =
  let* () = Budget.tick budget in
  match ty with
  | U32 | Bool -> Ok ()
  | Sum (a, b) ->
      let* () = branch_type budget a in
      branch_type budget b
  | Product (a, b) ->
      let* () = well_formed budget context a in
      well_formed budget context b
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
  | Inl (other, value) ->
      let* payload = infer budget phase context value in
      let ty = Sum (payload, other) in
      let* () = well_formed budget context ty in
      Ok ty
  | Inr (other, value) ->
      let* payload = infer budget phase context value in
      let ty = Sum (other, payload) in
      let* () = well_formed budget context ty in
      Ok ty
  | Case (result, value, a, b) ->
      let* () = branch_type budget result in
      let* ty = infer budget phase context value in
      (match ty with
       | Sum (left, right) ->
           let* expected = shift_ty budget 1 result in
           let* () = check_term budget phase
             ({ relevance = Runtime; ty = left } :: context) a expected in
           let* () = check_term budget phase
             ({ relevance = Runtime; ty = right } :: context) b expected in
           Ok result
       | U32 | Bool | Product _ | Eq _ | Pi _ -> Error Type_mismatch)
  | Pair (a, b) ->
      let* a = infer budget phase context a in
      let* b = infer budget phase context b in
      Ok (Product (a, b))
  | Fst a ->
      let* ty = infer budget phase context a in
      (match ty with Product (a, _) -> Ok a | U32 | Bool | Sum _ | Eq _ | Pi _ -> Error Type_mismatch)
  | Snd a ->
      let* ty = infer budget phase context a in
      (match ty with Product (_, b) -> Ok b | U32 | Bool | Sum _ | Eq _ | Pi _ -> Error Type_mismatch)
  | Compare (_, a, b) ->
      let* () = check_term budget phase context a U32 in
      let* () = check_term budget phase context b U32 in
      Ok Bool
  | If (c, a, b) ->
      let* () = check_term budget phase context c Bool in
      let* ty = infer budget phase context a in
      let* () = branch_type budget ty in
      let* () = check_term budget phase context b ty in
      Ok ty
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
       | U32 | Bool | Product _ | Sum _ | Eq _ -> Error Expected_function)
  | Let (r, a, value, body) ->
      let* () = well_formed budget context a in
      let* () = check_term budget (argument_phase phase r) context value a in
      let* b = infer budget phase ({ relevance = r; ty = a } :: context) body in
      subst_ty budget value b
  | Refl a ->
      let* () = check_term budget Ghost context a U32 in
      Ok (Eq (a, a))
  | Transport (family, a, b, proof, value) ->
      let* () = check_term budget Ghost context a U32 in
      let* () = check_term budget Ghost context b U32 in
      let* () = well_formed budget ({ relevance = Erased; ty = U32 } :: context) family in
      let* () = check_term budget Ghost context proof (Eq (a, b)) in
      let* source = subst_ty budget a family in
      let* target = subst_ty budget b family in
      let* () = check_term budget phase context value source in
      Ok target
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
    | Bool | Product _ | Sum _ | Eq _ | Pi (Erased, _, _) | Pi (Runtime, (Bool | Product _ | Sum _ | Eq _ | Pi _), _) -> Error Unsupported_export
  in
  let* parameters = export_arity 0 ty in
  Ok { source; parameters }
