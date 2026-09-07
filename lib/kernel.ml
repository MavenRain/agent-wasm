open Error
open Ast

type phase = Execute | Ghost
type binding = { relevance : relevance; ty : ty }
type checked = { source : term; parameters : int }
let term c = c.source
let arity c = c.parameters

module Field_names = Set.Make (String)

let record_labels budget fields =
  let rec walk seen = function
    | [] -> Ok ()
    | (name, _) :: rest ->
        let* () = Budget.tick budget in
        if Field_names.mem name seen then Error (Duplicate_field name)
        else walk (Field_names.add name seen) rest
  in
  match fields with
  | [] -> Error Empty_record
  | _ :: _ -> walk Field_names.empty fields

let rec lookup_field budget name = function
  | [] -> Error (Unknown_field name)
  | (label, value) :: rest ->
      let* () = Budget.tick budget in
      if label = name then Ok value else lookup_field budget name rest

let literal = function
  | Lit n -> Some n
  | RecordValue _ | Field _ | Pack _ | Value _ | Evidence _ | Inl _ | Inr _ | Case _ | Pair _ | Fst _ | Snd _ | Boolean _ | Compare _ | IfProof _ | If _ | Var _ | Add _ | Lam _ | App _ | Let _ | Refl _ | Transport _ | Ann _ -> None

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
       | RecordValue _ | Field _ | Pack _ | Value _ | Evidence _ | Var _ | Lit _ | Boolean _ | Pair _ | Fst _ | Snd _ | Compare _ | IfProof _ | If _
       | Add _ | Lam _ | App _ | Let _ | Refl _ | Transport _ | Ann _ | Case _ ->
           let* ty = normal_ty budget ty in
           let* a = normal budget a in
           let* b = normal budget b in
           Ok (Case (ty, value, a, b)))
  | Pair (a, b) ->
      let* a = normal budget a in
      let* b = normal budget b in
      Ok (Pair (a, b))
  | RecordValue fields ->
      let* fields = map_fields budget (normal budget) fields in
      Ok (RecordValue fields)
  | Field (value, name) ->
      let* value = normal budget value in
      (match value with
       | RecordValue fields -> lookup_field budget name fields
       | Field _ | Pack _ | Value _ | Evidence _ | Inl _ | Inr _ | Case _
       | Pair _ | Fst _ | Snd _ | Boolean _ | Compare _ | IfProof _ | If _
       | Var _ | Lit _ | Add _ | Lam _ | App _ | Let _ | Refl _ | Transport _
       | Ann _ -> Ok (Field (value, name)))
  | Fst a ->
      let* a = normal budget a in
      (match a with
       | Pair (a, _) -> Ok a
       | RecordValue _ | Field _ | Pack _ | Value _ | Evidence _ | Inl _ | Inr _ | Case _ | Var _ | Lit _ | Boolean _ | Fst _ | Snd _ | Compare _ | IfProof _ | If _ | Add _ | Lam _ | App _ | Let _ | Refl _ | Transport _ | Ann _ -> Ok (Fst a))
  | Snd a ->
      let* a = normal budget a in
      (match a with
       | Pair (_, b) -> Ok b
       | RecordValue _ | Field _ | Pack _ | Value _ | Evidence _ | Inl _ | Inr _ | Case _ | Var _ | Lit _ | Boolean _ | Fst _ | Snd _ | Compare _ | IfProof _ | If _ | Add _ | Lam _ | App _ | Let _ | Refl _ | Transport _ | Ann _ -> Ok (Snd a))
  | Pack (ty, value, proof) ->
      let* ty = normal_ty budget ty in
      let* value = normal budget value in
      let* proof = normal budget proof in
      Ok (Pack (ty, value, proof))
  | Value a ->
      let* a = normal budget a in
      (match a with
       | Pack (_, value, _) -> Ok value
       | RecordValue _ | Field _ | Value _ | Evidence _ | Inl _ | Inr _ | Case _ | Pair _ | Var _ | Lit _ | Boolean _
       | Fst _ | Snd _ | Compare _ | IfProof _ | If _ | Add _ | Lam _ | App _ | Let _ | Refl _ | Transport _ | Ann _ -> Ok (Value a))
  | Evidence a ->
      let* a = normal budget a in
      (match a with
       | Pack (_, _, proof) -> Ok proof
       | RecordValue _ | Field _ | Value _ | Evidence _ | Inl _ | Inr _ | Case _ | Pair _ | Var _ | Lit _ | Boolean _
       | Fst _ | Snd _ | Compare _ | IfProof _ | If _ | Add _ | Lam _ | App _ | Let _ | Refl _ | Transport _ | Ann _ -> Ok (Evidence a))
  | Compare (op, a, b) ->
      let* a = normal budget a in
      let* b = normal budget b in
      let result = Option.bind (literal a) (fun x -> Option.map (compare op x) (literal b)) in
      Ok (Option.fold ~none:(Compare (op, a, b)) ~some:(fun b -> Boolean b) result)
  | IfProof (ty, c, a, b) ->
      let* c = normal budget c in
      (match c with
       | Boolean selected ->
           let proof = Refl (Lit (if selected then 1L else 0L)) in
           let* body = subst_term budget proof (if selected then a else b) in
           normal budget body
       | RecordValue _ | Field _ | Pack _ | Value _ | Evidence _ | Inl _ | Inr _ | Case _ | Pair _
       | Fst _ | Snd _ | Var _ | Lit _ | Compare _ | IfProof _ | If _
       | Add _ | Lam _ | App _ | Let _ | Refl _ | Transport _ | Ann _ ->
           let* ty = normal_ty budget ty in
           let* a = normal budget a in
           let* b = normal budget b in
           Ok (IfProof (ty, c, a, b)))
  | If (c, a, b) ->
      let* c = normal budget c in
      (match c with
       | Boolean true -> normal budget a
       | Boolean false -> normal budget b
       | RecordValue _ | Field _ | Pack _ | Value _ | Evidence _ | Inl _ | Inr _ | Case _ | Pair _ | Fst _ | Snd _ | Var _ | Lit _ | Compare _ | IfProof _ | If _ | Add _ | Lam _ | App _ | Let _ | Refl _ | Transport _ | Ann _ ->
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
       | RecordValue _ | Field _ | Pack _ | Value _ | Evidence _ | Inl _ | Inr _ | Case _ | Pair _ | Fst _ | Snd _ | Boolean _ | Compare _ | IfProof _ | If _ | Var _ | Lit _ | Add _ | App _ | Let _ | Refl _ | Transport _ | Ann _ -> Ok (App (r, f, a)))
  | Let (_, _, value, body) ->
      let* value = normal budget value in
      let* body = subst_term budget value body in
      normal budget body
  | Refl a -> Result.map (fun a -> Refl a) (normal budget a)
  | Transport (family, a, b, proof, value) ->
      let* proof = normal budget proof in
      (match proof with
       | Refl _ -> normal budget value
       | RecordValue _ | Field _ | Pack _ | Value _ | Evidence _ | Var _ | Lit _ | Boolean _ | Inl _ | Inr _ | Case _ | Pair _ | Fst _ | Snd _ | Compare _ | IfProof _ | If _
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
  | Record fields ->
      let* () = Budget.tick budget in
      let* fields = map_fields budget (normal_ty budget) fields in
      Ok (Record fields)
  | Refine (a, proof) ->
      let* () = Budget.tick budget in
      let* a = normal_ty budget a in
      let* proof = normal_ty budget proof in
      Ok (Refine (a, proof))
  | Eq (a, b) ->
      let* () = Budget.tick budget in
      let* a = normal budget a in
      let* b = normal budget b in
      Ok (Eq (a, b))
  | Pi (r, a, b) ->
      let* () = Budget.tick budget in
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
  | Record fields ->
      let* () = record_labels budget fields in
      let* _ = map_fields budget (branch_type budget) fields in Ok ()
  | Refine (a, _) -> branch_type budget a
  | Eq _ | Pi _ -> Error Type_mismatch

let rec runtime_type budget ty =
  let* () = Budget.tick budget in
  match ty with
  | Eq _ -> Error Runtime_proof
  | U32 | Bool | Pi _ -> Ok ()
  | Product (a, b) | Sum (a, b) ->
      let* () = runtime_type budget a in runtime_type budget b
  | Record fields ->
      let* () = record_labels budget fields in
      let* _ = map_fields budget (runtime_type budget) fields in Ok ()
  | Refine (a, _) -> runtime_type budget a

let domain_allowed budget relevance ty =
  match relevance with
  | Erased -> Ok ()
  | Runtime -> runtime_type budget ty
let result_allowed budget phase ty =
  match phase with
  | Ghost -> Ok ty
  | Execute -> let* () = runtime_type budget ty in Ok ty

let rec well_formed budget context ty =
  let* () = Budget.tick budget in
  match ty with
  | U32 | Bool -> Ok ()
  | Sum (a, b) ->
      let* () = branch_type budget a in
      let* () = branch_type budget b in
      let* () = well_formed budget context a in
      well_formed budget context b
  | Product (a, b) ->
      let* () = well_formed budget context a in
      well_formed budget context b
  | Record fields ->
      let* () = record_labels budget fields in
      well_formed_fields budget context fields
  | Refine (a, proof) ->
      let* () = branch_type budget a in
      let* () = well_formed budget context a in
      (match proof with
       | Eq _ -> well_formed budget ({ relevance = Erased; ty = a } :: context) proof
       | U32 | Bool | Record _ | Product _ | Sum _ | Refine _ | Pi _ -> Error Type_mismatch)
  | Eq (a, b) ->
      let* () = check_term budget Ghost context a U32 in
      check_term budget Ghost context b U32
  | Pi (r, a, b) ->
      let* () = well_formed budget context a in
      let* () = domain_allowed budget r a in
      well_formed budget ({ relevance = r; ty = a } :: context) b
(* The field types of a record, without a second walk of that record's own
   labels. The caller checks those labels first. A nested record type still
   walks its own labels here, and the Execute phase walks the labels of a
   record result again in runtime_type. *)
and well_formed_fields budget context fields =
  let* _ = map_fields budget (fun ty ->
    let* () = branch_type budget ty in
    well_formed budget context ty) fields in
  Ok ()
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
      let* () = well_formed budget context result in
      let* ty = infer budget phase context value in
      (match ty with
       | Sum (left, right) ->
           let* expected = shift_ty budget 1 result in
           let* () = check_term budget phase
             ({ relevance = Runtime; ty = left } :: context) a expected in
           let* () = check_term budget phase
             ({ relevance = Runtime; ty = right } :: context) b expected in
           Ok result
       | U32 | Bool | Record _ | Product _ | Refine _ | Eq _ | Pi _ -> Error Type_mismatch)
  | Pair (a, b) ->
      let* a = infer budget phase context a in
      let* b = infer budget phase context b in
      Ok (Product (a, b))
  | RecordValue fields ->
      (* The labels are checked before the fields, so an empty or duplicate
         label list wins over a field's own inference error. The field types
         then need no second walk of these same labels. *)
      let* () = record_labels budget fields in
      let* fields = map_fields budget (infer budget phase context) fields in
      let* () = well_formed_fields budget context fields in
      Ok (Record fields)
  | Field (value, name) ->
      let* ty = infer budget phase context value in
      (match ty with
       | Record fields -> lookup_field budget name fields
       | U32 | Bool | Product _ | Sum _ | Refine _ | Eq _ | Pi _ -> Error Type_mismatch)
  | Fst a ->
      let* ty = infer budget phase context a in
      (match ty with Product (a, _) -> Ok a | U32 | Bool | Record _ | Sum _ | Refine _ | Eq _ | Pi _ -> Error Type_mismatch)
  | Snd a ->
      let* ty = infer budget phase context a in
      (match ty with Product (_, b) -> Ok b | U32 | Bool | Record _ | Sum _ | Refine _ | Eq _ | Pi _ -> Error Type_mismatch)
  | Pack (ty, value, proof) ->
      let* () = well_formed budget context ty in
      (match ty with
       | Refine (a, family) ->
           let* () = check_term budget phase context value a in
           let* evidence = subst_ty budget value family in
           let* () = check_term budget Ghost context proof evidence in
           Ok ty
       | U32 | Bool | Record _ | Product _ | Sum _ | Eq _ | Pi _ -> Error Type_mismatch)
  | Value a ->
      let* ty = infer budget phase context a in
      (match ty with
       | Refine (a, _) -> Ok a
       | U32 | Bool | Record _ | Product _ | Sum _ | Eq _ | Pi _ -> Error Type_mismatch)
  | Evidence a ->
      (match phase with
       | Execute -> Error Runtime_proof
       | Ghost ->
           let* ty = infer budget phase context a in
           (match ty with
            | Refine (_, family) -> subst_ty budget (Value a) family
            | U32 | Bool | Record _ | Product _ | Sum _ | Eq _ | Pi _ -> Error Type_mismatch))
  | Compare (_, a, b) ->
      let* () = check_term budget phase context a U32 in
      let* () = check_term budget phase context b U32 in
      Ok Bool
  | IfProof (result, c, a, b) ->
      let* () = branch_type budget result in
      let* () = well_formed budget context result in
      let* () = check_term budget phase context c Bool in
      let* expected = shift_ty budget 1 result in
      let indicator = If (c, Lit 1L, Lit 0L) in
      let branch outcome body =
        check_term budget phase
          ({ relevance = Erased; ty = Eq (indicator, Lit outcome) } :: context)
          body expected
      in
      let* () = branch 1L a in
      let* () = branch 0L b in
      Ok result
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
      let* () = domain_allowed budget r a in
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
       | U32 | Bool | Record _ | Product _ | Sum _ | Refine _ | Eq _ -> Error Expected_function)
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
  in result_allowed budget phase ty
and check_term budget phase context term expected =
  let* actual = infer budget phase context term in
  equivalent budget actual expected

let check budget source =
  let* ty = infer budget Execute [] source in
  let rec export_arity count = function
    | U32 -> Ok count
    | Pi (Runtime, U32, rest) -> export_arity (count + 1) rest
    | Bool | Record _ | Product _ | Sum _ | Refine _ | Eq _ | Pi (Erased, _, _) | Pi (Runtime, (Bool | Record _ | Product _ | Sum _ | Refine _ | Eq _ | Pi _), _) -> Error Unsupported_export
  in
  let* parameters = export_arity 0 ty in
  Ok { source; parameters }
