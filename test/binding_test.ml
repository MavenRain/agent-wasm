open Agent_wasm
open Error

(* This oracle resolves names through an explicit environment. Apply only
   combines already resolved children; Scope introduces a named binder. It
   never calls Ast.map_term, Ast.map_ty, shift, or substitution. Globally
   distinct local names keep the generic named substitution capture-free.
   These are bounded laws about well-scoped syntax, not typing proofs. *)
type _ named =
  | Pure : 'a -> 'a named
  | Name : string -> Ast.term named
  | Apply : ('a -> 'b) named * 'a named -> 'b named
  | Scope : string * 'a named -> 'a named

let one f a = Apply (Pure f, a)
let two f a b = Apply (one f a, b)
let three f a b c = Apply (two f a b, c)
let four f a b c d = Apply (three f a b c, d)
let five f a b c d e = Apply (four f a b c d, e)

let index name env =
  let rec walk n = function
    | [] -> Error (Unknown_name name)
    | head :: rest -> if head = name then Ok n else walk (n + 1) rest
  in
  walk 0 env

let rec resolve : type a. string list -> a named -> (a, Error.t) result =
  fun env syntax -> match syntax with
  | Pure value -> Ok value
  | Name name -> Result.map (fun n -> Ast.Var n) (index name env)
  | Apply (f, arg) ->
      let* f = resolve env f in
      let* arg = resolve env arg in
      Ok (f arg)
  | Scope (name, body) -> resolve (name :: env) body

let rec replace : type a.
  string -> Ast.term named -> a named -> a named =
  fun target value syntax -> match syntax with
  | Pure value -> Pure value
  | Name name -> if name = target then value else Name name
  | Apply (f, arg) -> Apply (replace target value f, replace target value arg)
  | Scope (name, body) ->
      if name = target then Scope (name, body)
      else Scope (name, replace target value body)

let lit n = Pure (Ast.Lit (Int64.of_int n))
let boolean b = Pure (Ast.Boolean b)
let pair = two (fun a b -> Ast.Pair (a, b))
let eq = two (fun a b -> Ast.Eq (a, b))
let ann = two (fun a ty -> Ast.Ann (a, ty))
let sigma a name b = two (fun a b -> Ast.Sigma (a, b)) a (Scope (name, b))
let refine a name b = two (fun a b -> Ast.Refine (a, b)) a (Scope (name, b))
let pi relevance a name b =
  two (fun a b -> Ast.Pi (relevance, a, b)) a (Scope (name, b))
let lam relevance a name b =
  two (fun a b -> Ast.Lam (relevance, a, b)) a (Scope (name, b))
let fields values = List.fold_right
  (fun (name, value) rest -> two (fun value rest -> (name, value) :: rest) value rest)
  values (Pure [])

(* Every probe mentions the target, each older variable, and every locally
   bound variable. Distinct markers also detect duplicated or reordered slots. *)
let probe env marker = List.fold_right
  (fun name rest -> pair (Name name) rest) env (lit marker)
let probe_ty env marker = eq (probe env marker) (probe (List.rev env) (marker + 1))

let nested_type env prefix =
  let p = prefix ^ "/pi" in
  let s = prefix ^ "/sigma" in
  let r = prefix ^ "/refine" in
  pi Ast.Erased (probe_ty env 101) p
    (sigma (probe_ty (p :: env) 102) s
      (refine (probe_ty (s :: p :: env) 103) r
        (probe_ty (r :: s :: p :: env) 104)))

let term_fixtures env =
  let t n = probe env n in
  let ty n = nested_type env ("term-type/" ^ string_of_int n) in
  let branch name marker = Scope (name, ann (probe (name :: env) marker)
    (nested_type (name :: env) (name ^ "/type"))) in
  [
    "var-target", Name "target";
    "var-older", Name "outer1";
    "literal", lit 42;
    "true", boolean true;
    "false", boolean false;
    "compare-equal", two (fun a b -> Ast.Compare (Ast.Equal, a, b)) (t 1) (t 2);
    "compare-less", two (fun a b -> Ast.Compare (Ast.Less, a, b)) (t 1) (t 2);
    "compare-less-equal", two (fun a b -> Ast.Compare (Ast.Less_equal, a, b)) (t 1) (t 2);
    "if", three (fun c a b -> Ast.If (c, a, b)) (t 1) (t 2) (t 3);
    "if-proof", four (fun ty c a b -> Ast.IfProof (ty, c, a, b))
      (ty 1) (t 2) (branch "if/yes" 3) (branch "if/no" 4);
    "add", two (fun a b -> Ast.Add (a, b)) (t 1) (t 2);
    "pair", pair (t 1) (t 2);
    "dependent-pair", three (fun ty a b -> Ast.DPair (ty, a, b)) (ty 1) (t 2) (t 3);
    "record", one (fun fields -> Ast.RecordValue fields)
      (fields ["second", t 1; "first", t 2]);
    "empty-record", Pure (Ast.RecordValue []);
    "field", one (fun value -> Ast.Field (value, "label")) (t 1);
    "fst", one (fun value -> Ast.Fst value) (t 1);
    "snd", one (fun value -> Ast.Snd value) (t 1);
    "pack", three (fun ty value proof -> Ast.Pack (ty, value, proof)) (ty 1) (t 2) (t 3);
    "value", one (fun value -> Ast.Value value) (t 1);
    "evidence", one (fun value -> Ast.Evidence value) (t 1);
    "inl", two (fun ty value -> Ast.Inl (ty, value)) (ty 1) (t 2);
    "inr", two (fun ty value -> Ast.Inr (ty, value)) (ty 1) (t 2);
    "case", four (fun ty value a b -> Ast.Case (ty, value, a, b))
      (ty 1) (t 2) (branch "case/left" 3) (branch "case/right" 4);
    "lam-runtime", lam Ast.Runtime (ty 1) "lam/run" (probe ("lam/run" :: env) 2);
    "lam-erased", lam Ast.Erased (ty 1) "lam/erase" (probe ("lam/erase" :: env) 2);
    "app-runtime", two (fun f a -> Ast.App (Ast.Runtime, f, a)) (t 1) (t 2);
    "app-erased", two (fun f a -> Ast.App (Ast.Erased, f, a)) (t 1) (t 2);
    "let-runtime", three (fun ty value body -> Ast.Let (Ast.Runtime, ty, value, body))
      (ty 1) (t 2) (branch "let/run" 3);
    "let-erased", three (fun ty value body -> Ast.Let (Ast.Erased, ty, value, body))
      (ty 1) (t 2) (branch "let/erase" 3);
    "refl", one (fun value -> Ast.Refl value) (t 1);
    "transport", five (fun family a b proof value -> Ast.Transport (family, a, b, proof, value))
      (Scope ("transport/index", nested_type ("transport/index" :: env) "transport/type"))
      (t 1) (t 2) (t 3) (t 4);
    "annotation", ann (t 1) (ty 2);
  ]

let type_fixtures env =
  let a = probe_ty env 1 in
  let b = probe_ty env 2 in
  [
    "u32", Pure Ast.U32;
    "bool", Pure Ast.Bool;
    "product", two (fun a b -> Ast.Product (a, b)) a b;
    "sigma", sigma a "sigma" (probe_ty ("sigma" :: env) 2);
    "record", one (fun fields -> Ast.Record fields) (fields ["second", a; "first", b]);
    "empty-record", Pure (Ast.Record []);
    "sum", two (fun a b -> Ast.Sum (a, b)) a b;
    "refine", refine a "refine" (probe_ty ("refine" :: env) 2);
    "eq", eq (probe env 1) (probe env 2);
    "pi-runtime", pi Ast.Runtime a "pi/run" (probe_ty ("pi/run" :: env) 2);
    "pi-erased", pi Ast.Erased a "pi/erase" (probe_ty ("pi/erase" :: env) 2);
    "nested-pi-sigma-refine", nested_type env "nested";
  ]

(* Exhaustive tags make additions to either AST sum require revisiting this
   suite. Coverage counts below concern the outer constructors of fixtures. *)
let term_tag = function
  | Ast.Var _ -> "var" | Ast.Lit _ -> "lit" | Ast.Boolean _ -> "boolean"
  | Ast.Compare _ -> "compare" | Ast.If _ -> "if" | Ast.IfProof _ -> "if-proof"
  | Ast.Add _ -> "add" | Ast.Pair _ -> "pair" | Ast.DPair _ -> "dpair"
  | Ast.RecordValue _ -> "record" | Ast.Field _ -> "field"
  | Ast.Fst _ -> "fst" | Ast.Snd _ -> "snd" | Ast.Pack _ -> "pack"
  | Ast.Value _ -> "value" | Ast.Evidence _ -> "evidence"
  | Ast.Inl _ -> "inl" | Ast.Inr _ -> "inr" | Ast.Case _ -> "case"
  | Ast.Lam _ -> "lam" | Ast.App _ -> "app" | Ast.Let _ -> "let"
  | Ast.Refl _ -> "refl" | Ast.Transport _ -> "transport" | Ast.Ann _ -> "ann"

let type_tag = function
  | Ast.U32 -> "u32" | Ast.Bool -> "bool" | Ast.Product _ -> "product"
  | Ast.Sigma _ -> "sigma" | Ast.Record _ -> "record" | Ast.Sum _ -> "sum"
  | Ast.Refine _ -> "refine" | Ast.Eq _ -> "eq" | Ast.Pi _ -> "pi"

(* The expected tags are lists, not counts. A new constructor without a
   fixture then fails coverage even when another tag disappears. *)
let all_term_tags = List.sort_uniq String.compare
  ["add"; "ann"; "app"; "boolean"; "case"; "compare"; "dpair"; "evidence";
   "field"; "fst"; "if"; "if-proof"; "inl"; "inr"; "lam"; "let"; "lit";
   "pack"; "pair"; "record"; "refl"; "snd"; "transport"; "value"; "var"]

let all_type_tags = List.sort_uniq String.compare
  ["bool"; "eq"; "pi"; "product"; "record"; "refine"; "sigma"; "sum"; "u32"]

(* Deterministic generation bounds recursion at five constructor layers.
   Paths make local names globally distinct, including sibling branches.
   A leaf reads the whole seed, and the eight index slots reach every name
   of the deepest scope. Leaves then differ instead of repeating one name. *)
let mix seed salt = (seed * 17 + salt * 31 + 7) mod 997
let pick env seed = Option.fold ~none:(lit seed) ~some:(fun name -> Name name)
  (List.nth_opt env (seed mod 8))

let rec gen_term depth env path seed =
  let t slot = gen_term (depth - 1) env (path ^ "/t" ^ string_of_int slot) (mix seed slot) in
  let ty slot = gen_type (depth - 1) env (path ^ "/y" ^ string_of_int slot) (mix seed slot) in
  let bound slot =
    let name = path ^ "/binder" ^ string_of_int slot in
    Scope (name, gen_term (depth - 1) (name :: env) (name ^ "/body") (mix seed slot)) in
  let relevance = if seed mod 2 = 0 then Ast.Runtime else Ast.Erased in
  if depth = 0 then pick env seed else
  match seed mod 25 with
  | 0 -> pick env seed
  | 1 -> lit seed
  | 2 -> boolean (seed mod 2 = 0)
  | 3 -> two (fun a b -> Ast.Compare (Ast.Less_equal, a, b)) (t 1) (t 2)
  | 4 -> three (fun c a b -> Ast.If (c, a, b)) (t 1) (t 2) (t 3)
  | 5 -> four (fun ty c a b -> Ast.IfProof (ty, c, a, b)) (ty 1) (t 2) (bound 3) (bound 4)
  | 6 -> two (fun a b -> Ast.Add (a, b)) (t 1) (t 2)
  | 7 -> pair (t 1) (t 2)
  | 8 -> three (fun ty a b -> Ast.DPair (ty, a, b)) (ty 1) (t 2) (t 3)
  | 9 -> one (fun fields -> Ast.RecordValue fields) (fields ["z", t 1; "a", t 2])
  | 10 -> one (fun value -> Ast.Field (value, "z")) (t 1)
  | 11 -> one (fun value -> Ast.Fst value) (t 1)
  | 12 -> one (fun value -> Ast.Snd value) (t 1)
  | 13 -> three (fun ty value proof -> Ast.Pack (ty, value, proof)) (ty 1) (t 2) (t 3)
  | 14 -> one (fun value -> Ast.Value value) (t 1)
  | 15 -> one (fun value -> Ast.Evidence value) (t 1)
  | 16 -> two (fun ty value -> Ast.Inl (ty, value)) (ty 1) (t 2)
  | 17 -> two (fun ty value -> Ast.Inr (ty, value)) (ty 1) (t 2)
  | 18 -> four (fun ty value a b -> Ast.Case (ty, value, a, b)) (ty 1) (t 2) (bound 3) (bound 4)
  | 19 -> two (fun ty body -> Ast.Lam (relevance, ty, body)) (ty 1) (bound 2)
  | 20 -> two (fun f a -> Ast.App (relevance, f, a)) (t 1) (t 2)
  | 21 -> three (fun ty value body -> Ast.Let (relevance, ty, value, body)) (ty 1) (t 2) (bound 3)
  | 22 -> one (fun value -> Ast.Refl value) (t 1)
  | 23 ->
      let name = path ^ "/index" in
      five (fun family a b proof value -> Ast.Transport (family, a, b, proof, value))
        (Scope (name, gen_type (depth - 1) (name :: env) (name ^ "/family") (mix seed 1)))
        (t 2) (t 3) (t 4) (t 5)
  | _ -> ann (t 1) (ty 2)
and gen_type depth env path seed =
  let t slot = gen_term (depth - 1) env (path ^ "/t" ^ string_of_int slot) (mix seed slot) in
  let ty slot = gen_type (depth - 1) env (path ^ "/y" ^ string_of_int slot) (mix seed slot) in
  let bound slot =
    let name = path ^ "/binder" ^ string_of_int slot in
    Scope (name, gen_type (depth - 1) (name :: env) (name ^ "/body") (mix seed slot)) in
  if depth = 0 then eq (pick env seed) (pick env (seed + 1)) else
  match seed mod 9 with
  | 0 -> Pure Ast.U32
  | 1 -> Pure Ast.Bool
  | 2 -> two (fun a b -> Ast.Product (a, b)) (ty 1) (ty 2)
  | 3 -> two (fun a b -> Ast.Sigma (a, b)) (ty 1) (bound 2)
  | 4 -> one (fun fields -> Ast.Record fields) (fields ["z", ty 1; "a", ty 2])
  | 5 -> two (fun a b -> Ast.Sum (a, b)) (ty 1) (ty 2)
  | 6 -> two (fun a b -> Ast.Refine (a, b)) (ty 1) (bound 2)
  | 7 -> eq (t 1) (t 2)
  | _ -> two (fun a b -> Ast.Pi ((if seed mod 2 = 0 then Ast.Runtime else Ast.Erased), a, b))
      (ty 1) (bound 2)

let outer = ["outer0"; "outer1"]
let context = "target" :: outer

let replacements = [
  "closed", lit 42;
  "open-nearest", Name "outer0";
  "open-older", pair (Name "outer1") (Name "outer0");
  "open-with-binders", lam Ast.Erased (eq (Name "outer0") (Name "outer1")) "replacement/local"
    (ann (pair (Name "replacement/local") (Name "outer1"))
      (sigma (eq (Name "replacement/local") (Name "outer0")) "replacement/index"
        (eq (Name "replacement/local") (Name "replacement/index"))));
]

let same expected actual = if expected = actual then Ok () else Error (Backend "named oracle mismatch")
let budget () = Budget.create 1_000_000

let laws shift subst category samples = List.concat_map (fun (name, source) ->
  let label law = category ^ "/" ^ name ^ "/" ^ law in
  let shifts = List.map (fun delta -> label ("shift/" ^ string_of_int delta), fun () ->
    let extra = List.init (abs delta) (fun n -> "unused/" ^ string_of_int n) in
    let before, after = if delta < 0 then extra @ context, context else context, extra @ context in
    let* input = resolve before source in
    let* expected = resolve after source in
    let* actual = shift (budget ()) delta input in
    same expected actual) [0; 1; 3; -1; -3] in
  let substitutions = List.map (fun (replacement_name, replacement) ->
    label ("subst/" ^ replacement_name), fun () ->
      let* input = resolve context source in
      let* value = resolve outer replacement in
      let* expected = resolve outer (replace "target" replacement source) in
      let* actual = subst (budget ()) value input in
      same expected actual) replacements in
  shifts @ substitutions) samples

let generated generator = List.concat_map (fun depth -> List.init 75 (fun seed ->
  let name = "depth" ^ string_of_int depth ^ "/seed" ^ string_of_int seed in
  name, generator depth context ("generated/" ^ name) seed)) [1; 2; 3; 4; 5]

(* Distinct resolved samples measure generator collapse. A duplicated tree
   repeats laws that an earlier sample already checked. *)
let distinct samples = List.length (List.sort_uniq compare
  (List.filter_map (fun (_, syntax) -> Result.to_option (resolve context syntax))
    samples))

let error_is expected actual = Result.fold
  ~ok:(fun _ -> Error (Backend "expected binding error"))
  ~error:(fun actual -> if actual = expected then Ok () else Error actual) actual

let boundary_cases = [
  "negative-term-index/shift", (fun () ->
    error_is (Invalid_index (-1)) (Ast.shift_term (budget ()) 3 (Ast.Var (-1))));
  "negative-term-index/subst", (fun () ->
    error_is (Invalid_index (-1)) (Ast.subst_term (budget ()) (Ast.Lit 1L) (Ast.Var (-1))));
  "negative-type-index/shift", (fun () ->
    error_is (Invalid_index (-1)) (Ast.shift_ty (budget ()) 3 (Ast.Eq (Ast.Var (-1), Ast.Lit 1L))));
  "negative-type-index/subst", (fun () ->
    error_is (Invalid_index (-1)) (Ast.subst_ty (budget ()) (Ast.Lit 1L) (Ast.Eq (Ast.Var (-1), Ast.Lit 1L))));
  "removed-outer-term-index", (fun () ->
    error_is (Invalid_index (-1)) (Ast.shift_term (budget ()) (-1) (Ast.Var 0)));
  "removed-outer-under-lambda", (fun () ->
    error_is (Invalid_index 0)
      (Ast.shift_term (budget ()) (-1) (Ast.Lam (Ast.Runtime, Ast.U32, Ast.Var 1))));
  "removed-outer-under-sigma", (fun () ->
    error_is (Invalid_index 0)
      (Ast.shift_ty (budget ()) (-1) (Ast.Sigma (Ast.U32, Ast.Eq (Ast.Var 0, Ast.Var 1)))));
  "removed-outer-under-three-type-binders", (fun () ->
    error_is (Invalid_index 2) (Ast.shift_ty (budget ()) (-1)
      (Ast.Pi (Ast.Erased, Ast.U32, Ast.Sigma (Ast.U32,
        Ast.Refine (Ast.U32, Ast.Eq (Ast.Var 2, Ast.Var 3)))))));
  "removed-outer-in-transport-family", (fun () ->
    error_is (Invalid_index 0) (Ast.shift_term (budget ()) (-1)
      (Ast.Transport (Ast.Eq (Ast.Var 0, Ast.Var 1), Ast.Lit 1L,
        Ast.Lit 2L, Ast.Refl (Ast.Lit 1L), Ast.Lit 3L))));
  "closed-binder-survives-negative-shift", (fun () ->
    let body = Ast.Lam (Ast.Runtime, Ast.U32, Ast.Var 0) in
    let* actual = Ast.shift_term (budget ()) (-3) body in same body actual);
  "substitution-removes-outer-index", (fun () ->
    let body = Ast.Lam (Ast.Runtime, Ast.U32,
      Ast.Pair (Ast.Var 0, Ast.Pair (Ast.Var 1, Ast.Pair (Ast.Var 2, Ast.Var 3)))) in
    let expected = Ast.Lam (Ast.Runtime, Ast.U32,
      Ast.Pair (Ast.Var 0, Ast.Pair (Ast.Var 2, Ast.Pair (Ast.Var 1, Ast.Var 2)))) in
    let* actual = Ast.subst_term (budget ()) (Ast.Var 1) body in same expected actual);
]

let coverage tag expected fixtures =
  let* tags = List.fold_left (fun acc (_, syntax) ->
    let* acc = acc in
    let* value = resolve context syntax in
    Ok (tag value :: acc)) (Ok []) fixtures in
  if List.sort_uniq String.compare tags = expected then Ok ()
  else Error (Backend "constructor coverage changed")

let () =
  let terms = term_fixtures context in
  let types = type_fixtures context in
  let term_samples = generated gen_term in
  let type_samples = generated gen_type in
  let cases = [
    "all-term-constructors", (fun () -> coverage term_tag all_term_tags terms);
    "all-type-constructors", (fun () -> coverage type_tag all_type_tags types);
  ] @ laws Ast.shift_term Ast.subst_term "term-fixture" terms
    @ laws Ast.shift_ty Ast.subst_ty "type-fixture" types
    @ laws Ast.shift_term Ast.subst_term "term-generated" term_samples
    @ laws Ast.shift_ty Ast.subst_ty "type-generated" type_samples
    @ boundary_cases in
  let failures = List.fold_left (fun failures (name, test) ->
    Result.fold ~ok:(fun () -> failures)
      ~error:(fun error -> (name ^ ": " ^ Error.message error) :: failures) (test ())) [] cases in
  List.iter prerr_endline (List.rev failures);
  Printf.printf
    "binding: %d cases, %d failures (%d term and %d type constructors; \
     %d generated samples, %d distinct)\n"
    (List.length cases) (List.length failures)
    (List.length all_term_tags) (List.length all_type_tags)
    (List.length term_samples + List.length type_samples)
    (distinct term_samples + distinct type_samples);
  if failures <> [] then exit 1
