open Agent_wasm
open Error

let compile body = Compiler.compile ("(export main " ^ body ^ ")")
let accepted body = Result.map (fun _artifact -> ()) (compile body)
let rejected expected body =
  Result.fold
    ~ok:(fun _artifact -> Error (Backend "unexpected acceptance"))
    ~error:(fun actual -> if actual = expected then Ok () else Error actual)
    (compile body)

let kernel_rejects expected body =
  Result.fold
    ~ok:(fun _checked -> Error (Backend "unexpected acceptance"))
    ~error:(fun actual -> if actual = expected then Ok () else Error actual)
    (Compiler.check ("(export main " ^ body ^ ")"))

let same_output a b =
  let* a = compile a in
  let* b = compile b in
  if a.wasm = b.wasm && a.runtime = b.runtime then Ok ()
  else Error (Backend "erasure changed output")

let dependent n x proof =
  "(app erase (app run (app erase " ^
  "(fn (erase n u32) (fn (run x u32) (fn (erase p (eq x n)) x))) " ^
  n ^ ") " ^ x ^ ") " ^ proof ^ ")"

(* Direct AST clients bypass the parser's depth limit. *)
let emit_parameters count =
  let budget = Budget.create 1_000_000 in
  let body = List.fold_left (fun body _ -> Ast.Lam (Ast.Runtime, Ast.U32, body))
    (Ast.Add (Ast.Var (count - 1), Ast.Var 0)) (List.init count Fun.id) in
  let* checked = Kernel.check budget body in
  let* runtime = Erase.run budget checked in
  Wasm.emit budget runtime

let cases = [
  "refinement fixed compilation budget", (fun () ->
    let source = "(export main (fn (run n u32) (value (case (refine (x u32) (eq x n)) (if (u32-eq n 0) (inl bool n) (inr u32 false)) (a (pack (refine (x u32) (eq x n)) n (refl n))) (b (pack (refine (x u32) (eq x n)) n (refl n)))))))" in
    let* artifact = Compiler.compile ~fuel:332 source in
    let* () = if artifact.steps = 332 then Ok () else Error (Backend "refinement budget changed") in
    Result.fold ~ok:(fun _ -> Error (Backend "refinement fuel boundary accepted"))
      ~error:(function Budget_exhausted -> Ok () | e -> Error e)
      (Compiler.compile ~fuel:331 source));
  "refinement scalar erasure", (fun () -> same_output
    "(fn (run n u32) (value (pack (refine (x u32) (eq x (add n 1))) (add n 1) (refl (add n 1)))))"
    "(fn (run n u32) (add n 1))");
  "refinement abstract evidence", (fun () -> accepted
    "(fn (run n u32) (let (run p (refine (x u32) (eq x n))) (pack (refine (x u32) (eq x n)) n (refl n)) (let (erase e (eq (value p) n)) (evidence p) (value p))))");
  "refinement proof can be erased variable", (fun () -> same_output
    "(fn (run n u32) (let (erase e (eq n n)) (refl n) (value (pack (refine (x u32) (eq x n)) n e))))"
    "(fn (run n u32) n)");
  "refinement product payload", (fun () -> same_output
    "(fn (run n u32) (snd (value (pack (refine (p (product bool u32)) (eq (snd p) n)) (pair true n) (refl n)))))"
    "(fn (run n u32) (snd (pair true n)))");
  "refinement boolean payload", (fun () -> accepted
    "(if (value (pack (refine (b bool) (eq (if b 1 0) 1)) true (refl 1))) 7 9)");
  "refinement nested payload", (fun () -> accepted
    "(value (value (pack (refine (p (refine (x u32) (eq x 7))) (eq (value p) 7)) (pack (refine (x u32) (eq x 7)) 7 (refl 7)) (refl 7))))");
  "refinement false proof", (fun () -> kernel_rejects Type_mismatch
    "(value (pack (refine (x u32) (eq x 7)) 8 (refl 7)))");
  "refinement wrong proof type", (fun () -> kernel_rejects Type_mismatch
    "(value (pack (refine (x u32) (eq x 7)) 7 7))");
  "refinement wrong payload", (fun () -> kernel_rejects Type_mismatch
    "(value (pack (refine (x u32) (eq x 7)) true (refl 7)))");
  "refinement annotation required", (fun () -> kernel_rejects Type_mismatch
    "(value (pack u32 7 (refl 7)))");
  "refinement family must be equality", (fun () -> kernel_rejects Type_mismatch
    "(value (pack (refine (x u32) u32) 7 7))");
  "refinement bad equality index", (fun () -> kernel_rejects Type_mismatch
    "(value (pack (refine (x bool) (eq x x)) true (refl 7)))");
  "refinement function payload rejected", (fun () -> kernel_rejects Type_mismatch
    "(pack (refine (f (pi (run x u32) u32)) (eq (app run f 0) 0)) (fn (run x u32) x) (refl 0))");
  "refinement evidence payload rejected", (fun () -> kernel_rejects Type_mismatch
    "(fn (run p (refine (x (eq 0 0)) (eq 0 0))) 0)");
  "refinement runtime evidence", (fun () -> kernel_rejects Runtime_proof
    "(evidence (pack (refine (x u32) (eq x 7)) 7 (refl 7)))");
  "refinement erased payload", (fun () -> kernel_rejects (Erased_use 0)
    "(let (erase n u32) 7 (value (pack (refine (x u32) (eq x n)) n (refl n))))");
  "refinement erased package", (fun () -> kernel_rejects (Erased_use 0)
    "(let (erase p (refine (x u32) (eq x 7))) (pack (refine (x u32) (eq x 7)) 7 (refl 7)) (value p))");
  "refinement ghost package evidence", (fun () -> same_output
    "(let (erase p (refine (x u32) (eq x 7))) (pack (refine (x u32) (eq x 7)) 7 (refl 7)) (let (erase e (eq (value p) 7)) (evidence p) 42))"
    "42");
  "refinement value needs package", (fun () -> kernel_rejects Type_mismatch "(value 7)");
  "refinement evidence needs package", (fun () -> kernel_rejects Type_mismatch
    "(let (erase e (eq 7 7)) (evidence 7) 0)");
  "refinement export", (fun () -> kernel_rejects Unsupported_export
    "(pack (refine (x u32) (eq x 7)) 7 (refl 7))");
  "refinement export parameter", (fun () -> kernel_rejects Unsupported_export
    "(fn (run p (refine (x u32) (eq x 7))) (value p))");
  "refinement closed value conversion", (fun () -> accepted
    "(let (erase e (eq (value (pack (refine (x u32) (eq x 7)) (add 3 4) (refl 7))) 7)) (refl 7) 0)");
  "refinement closed evidence conversion", (fun () -> accepted
    "(let (erase e (eq (transport (i u32) 7 7 (evidence (pack (refine (x u32) (eq x 7)) 7 (refl 7))) 9) 9)) (refl 9) 0)");
  "refinement open value stays symbolic", (fun () -> kernel_rejects Type_mismatch
    "(let (erase f (pi (run p (refine (x u32) (eq x 7))) (eq (value p) 7))) (fn (run p (refine (x u32) (eq x 7))) (refl 7)) 0)");
  "refinement open evidence stays symbolic", (fun () -> kernel_rejects Type_mismatch
    "(let (erase f (pi (run p (refine (x u32) (eq x 7))) (eq (transport (i u32) (value p) 7 (evidence p) 9) 9))) (fn (run p (refine (x u32) (eq x 7))) (refl 9)) 0)");
  "refinement open projections normalize", (fun () -> accepted
    "(let (erase f (pi (run p (refine (x u32) (eq x 7))) (eq (value (app run (fn (run q (refine (x u32) (eq x 7))) q) p)) (value p)))) (fn (run p (refine (x u32) (eq x 7))) (refl (value p))) 0)");
  "refinement transport indexed family", (fun () -> accepted
    "(let (erase f (pi (erase a u32) (pi (erase b u32) (pi (erase e (eq a b)) (pi (run p (refine (x u32) (eq x a))) (refine (x u32) (eq x b))))))) (fn (erase a u32) (fn (erase b u32) (fn (erase e (eq a b)) (fn (run p (refine (x u32) (eq x a))) (transport (i (refine (x u32) (eq x i))) a b e p))))) 0)");
  "refinement transport sum family", (fun () -> accepted
    "(let (erase f (pi (erase a u32) (pi (erase b u32) (pi (erase e (eq a b)) (pi (run s (sum bool (refine (x u32) (eq x a)))) (sum bool (refine (x u32) (eq x b)))))))) (fn (erase a u32) (fn (erase b u32) (fn (erase e (eq a b)) (fn (run s (sum bool (refine (x u32) (eq x a)))) (transport (i (sum bool (refine (x u32) (eq x i)))) a b e s))))) 0)");
  "refinement transport at execute erases to payload", (fun () -> same_output
    "(fn (run n u32) (let (erase same (eq (add n 1) (add n 1))) (refl (add n 1)) (value (transport (i (refine (item u32) (eq item i))) (add n 1) (add n 1) same (pack (refine (item u32) (eq item (add n 1))) (add n 1) same)))))"
    "(fn (run n u32) (add n 1))");
  "refinement inactive alternative zero fill", (fun () -> same_output
    "(fn (run n u32) (case u32 (inr (refine (p (product u32 u32)) (eq (fst p) 0)) n) (a (fst (value a))) (b b)))"
    "(fn (run n u32) (case u32 (inr (product u32 u32) n) (a (fst a)) (b b)))");
  "refinement projection stuck on if", (fun () -> kernel_rejects Type_mismatch
    "(fn (run c bool) (let (erase e (eq (value (if c (pack (refine (item u32) (eq item 7)) 7 (refl 7)) (pack (refine (item u32) (eq item 7)) 7 (refl 7)))) 7)) (refl 7) 7))");
  "refinement family checked inside sum", (fun () -> kernel_rejects Type_mismatch
    "(case u32 (inl (refine (x u32) (eq true x)) 7) (x x) (p 0))");
  "refinement nested family checked", (fun () -> kernel_rejects Type_mismatch
    "(fn (run p (refine (x (refine (y u32) (eq true y))) (eq 0 0))) 0)");
  "refinement case result family checked", (fun () -> kernel_rejects Type_mismatch
    "(value (case (refine (x u32) (eq true x)) (inl u32 0) (a (pack (refine (x u32) (eq x x)) a (refl a))) (b (pack (refine (x u32) (eq x x)) b (refl b)))))");
  "refinement case result formation before conversion", (fun () -> kernel_rejects Type_mismatch
    "(value (case (refine (x u32) (eq (if true x false) x)) (inl u32 0) (a (pack (refine (x u32) (eq x x)) a (refl a))) (b (pack (refine (x u32) (eq x x)) b (refl b)))))");
  "refinement indexed case result", (fun () -> accepted
    "(fn (run n u32) (value (case (refine (x u32) (eq x n)) (inl bool 0) (a (pack (refine (x u32) (eq x n)) n (refl n))) (b (pack (refine (x u32) (eq x n)) n (refl n))))))");
  "refinement branch evidence mismatch", (fun () -> kernel_rejects Type_mismatch
    "(value (if true (pack (refine (x u32) (eq x 7)) 7 (refl 7)) (pack (refine (x u32) (eq x 8)) 8 (refl 8))))");
  "refinement no comparison reflection", (fun () -> kernel_rejects Type_mismatch
    "(fn (run n u32) (if (u32-eq n 7) (value (pack (refine (x u32) (eq x 7)) n (refl n))) 0))");
  "refinement binder reserved", (fun () -> rejected (Parse "binder name is reserved for literals")
    "(value (pack (refine (true u32) (eq 7 7)) 7 (refl 7)))");
  "refinement binder absent from payload", (fun () -> rejected (Unknown_name "x")
    "(value (pack (refine (x u32) (eq x x)) x (refl 7)))");
  "refinement binder absent from proof", (fun () -> rejected (Unknown_name "x")
    "(value (pack (refine (x u32) (eq x x)) 7 (refl x)))");
  "refinement substitution through nested binders", (fun () ->
    let open Ast in
    let inner = Refine (U32, Eq (Var 0, Var 1)) in
    let outer = Refine (inner, Eq (Value (Var 0), Var 1)) in
    let replacement = Add (Var 0, Lit 1L) in
    let* actual = subst_ty (Budget.create 1000) replacement outer in
    let lifted = Add (Var 1, Lit 1L) in
    let expected = Refine (Refine (U32, Eq (Var 0, lifted)),
      Eq (Value (Var 0), lifted)) in
    if actual = expected then Ok () else Error (Backend "refinement family capture"));
  "refinement constructor has no binder", (fun () ->
    let open Ast in
    let annotation = Refine (U32, Eq (Var 0, Var 1)) in
    let body = Pack (annotation, Var 0, Evidence (Var 0)) in
    let replacement = Value (Var 0) in
    let* actual = subst_term (Budget.create 1000) replacement body in
    let expected = Pack (Refine (U32, Eq (Var 0, Value (Var 1))),
      replacement, Evidence replacement) in
    if actual = expected then Ok () else Error (Backend "refinement constructor capture"));
  "sum stuck handler binder capture", (fun () -> accepted
    "(fn (run w u32) (let (erase p (eq (fst (app run (fn (run s (sum u32 u32)) (case (product u32 u32) s (x (pair x w)) (y (pair y y)))) (inl u32 1))) 1)) (refl 1) 0))");
  "sum stuck handler wrong endpoint", (fun () -> kernel_rejects Type_mismatch
    "(fn (run w u32) (let (erase p (eq (fst (app run (fn (run s (sum u32 u32)) (case (product u32 u32) s (x (pair x w)) (y (pair y y)))) (inl u32 1))) 2)) (refl 2) 0))");
  "sum fixed compilation budget", (fun () ->
    let source = "(export main (fst (case (product u32 bool) (if true (inl bool (add 1 2)) (inr u32 false)) (x (pair x true)) (b (pair 0 b)))))" in
    let* artifact = Compiler.compile ~fuel:217 source in
    let* () = if artifact.steps = 217 then Ok () else Error (Backend "sum budget changed") in
    Result.fold ~ok:(fun _ -> Error (Backend "sum fuel boundary accepted"))
      ~error:(function Budget_exhausted -> Ok () | e -> Error e)
      (Compiler.compile ~fuel:216 source));
  "sum open branches normalize", (fun () -> accepted
    "(app run (fn (run s (sum u32 u32)) (let (erase p (eq (case u32 s (x (add 1 2)) (y (add 3 4))) (case u32 s (x 3) (y 7)))) (refl (case u32 s (x 3) (y 7))) 0)) (inl u32 7))");
  "sum transported shape", (fun () -> accepted
    "(case u32 (transport (i (sum bool u32)) 0 0 (refl 0) (inr bool 7)) (b (if b 1 2)) (x x))");
  "sum left", (fun () -> accepted "(case u32 (inl bool 7) (x x) (b (if b 1 2)))");
  "sum right", (fun () -> accepted "(case u32 (inr u32 true) (x x) (b (if b 1 2)))");
  "sum closed left conversion", (fun () -> accepted
    "(let (erase p (eq (case u32 (inl bool 7) (x (add x 1)) (b 99)) 8)) (refl 8) 0)");
  "sum closed right conversion", (fun () -> accepted
    "(let (erase p (eq (case u32 (inr u32 true) (x 99) (b (if b 8 9))) 8)) (refl 8) 0)");
  "sum wrong conversion", (fun () -> kernel_rejects Type_mismatch
    "(let (erase p (eq (case u32 (inl u32 7) (x x) (y 8)) 8)) (refl 8) 0)");
  "sum open conversion", (fun () -> accepted
    "(app run (fn (run s (sum u32 u32)) (let (erase p (eq (case u32 s (x (add x 0)) (y y)) (case u32 s (x (add x 0)) (y y)))) (refl (case u32 s (x (add x 0)) (y y))) 0)) (inl u32 7))");
  "sum open branches stay distinct", (fun () -> kernel_rejects Type_mismatch
    "(app run (fn (run s (sum u32 u32)) (let (erase p (eq (case u32 s (x x) (y 1)) (case u32 s (x x) (y 2)))) (refl (case u32 s (x x) (y 1))) 0)) (inl u32 7))");
  "sum conversion capture", (fun () -> accepted
    "(fn (run n u32) (let (erase p (eq (app run (fn (run z u32) (case u32 (inr u32 z) (x n) (x (add n x)))) 3) (add n 3))) (refl (add n 3)) 0))");
  "sum proof erasure", (fun () -> same_output
    "(let (erase s (sum u32 bool)) (inl bool 7) 42)" "42");
  "sum runtime ghost capture", (fun () -> kernel_rejects (Erased_use 1)
    "(let (erase n u32) 7 (case u32 (inl u32 1) (x x) (y n)))");
  "sum erased scrutinee", (fun () -> kernel_rejects (Erased_use 0)
    "(let (erase s (sum u32 bool)) (inl bool 7) (case u32 s (x x) (b 0)))");
  "sum scalar scrutinee", (fun () -> kernel_rejects Type_mismatch "(case u32 1 (x x) (y y))");
  "sum left branch mismatch", (fun () -> kernel_rejects Type_mismatch "(case u32 (inr u32 1) (x true) (y y))");
  "sum right branch mismatch", (fun () -> kernel_rejects Type_mismatch "(case u32 (inl u32 1) (x x) (y false))");
  "sum annotation mismatch", (fun () -> kernel_rejects Type_mismatch
    "(let (run s (sum bool u32)) (inl u32 7) 0)");
  "sum mismatched conditional", (fun () -> kernel_rejects Type_mismatch
    "(let (run s (sum u32 bool)) (if true (inl bool 7) (inr bool false)) 0)");
  "sum left evidence type", (fun () -> kernel_rejects Type_mismatch
    "(let (erase s (sum (eq 0 0) u32)) (inr (eq 0 0) 7) 0)");
  "sum right evidence type", (fun () -> kernel_rejects Type_mismatch
    "(let (erase s (sum u32 (eq 0 0))) (inl (eq 0 0) 7) 0)");
  "sum nested function type", (fun () -> kernel_rejects Type_mismatch
    "(let (erase s (sum u32 (product bool (pi (run x u32) u32)))) (inl (product bool (pi (run x u32) u32)) 7) 0)");
  "sum function payload", (fun () -> kernel_rejects Type_mismatch
    "(let (run s (sum u32 u32)) (inl u32 (fn (run x u32) x)) 0)");
  "sum case function result", (fun () -> kernel_rejects Type_mismatch
    "(case (pi (run x u32) u32) (inl u32 1) (a (fn (run x u32) x)) (b (fn (run x u32) x)))");
  "sum case proof result", (fun () -> kernel_rejects Type_mismatch
    "(let (erase p (eq 0 0)) (case (eq 0 0) (inl u32 1) (a (refl 0)) (b (refl 0))) 0)");
  "sum export", (fun () -> kernel_rejects Unsupported_export "(inl bool 7)");
  "sum parameter export", (fun () -> kernel_rejects Unsupported_export "(fn (run s (sum u32 bool)) 0)");
  "sum projection", (fun () -> kernel_rejects Type_mismatch "(fst (inl bool 7))");
  "sum application", (fun () -> kernel_rejects Expected_function "(app run (inl bool 7) 0)");
  "sum left reserved binder", (fun () -> rejected (Parse "binder name is reserved for literals")
    "(case u32 (inl u32 1) (true 0) (y y))");
  "sum right reserved binder", (fun () -> rejected (Parse "binder name is reserved for literals")
    "(case u32 (inl u32 1) (x x) (5 0))");
  "sum binder scope", (fun () -> rejected (Unknown_name "x") "(case u32 (inl u32 1) (x x) (y x))");
  "transport family capture avoidance", (fun () ->
    let open Ast in
    let family = Pi (Erased, Eq (Var 0, Var 1), Eq (Var 1, Var 2)) in
    let body = Transport (family, Var 0, Var 0, Refl (Var 0), Var 0) in
    let replacement = Add (Var 0, Lit 1L) in
    let* actual = subst_term (Budget.create 1000) replacement body in
    let expected_family = Pi (Erased,
      Eq (Var 0, Add (Var 1, Lit 1L)), Eq (Var 1, Add (Var 2, Lit 1L))) in
    let expected = Transport (expected_family, replacement, replacement,
      Refl replacement, replacement) in
    if actual = expected then Ok () else Error (Backend "transport captured family variable"));
  "transport exact budget", (fun () ->
    let source = "(export main (fn (run n u32) (transport (x u32) n n (refl n) (add n 1))))" in
    let* artifact = Compiler.compile source in
    let* exact = Compiler.compile ~fuel:artifact.steps source in
    if artifact.wasm <> exact.wasm then Error (Backend "transport nondeterministic output")
    else Result.fold ~ok:(fun _ -> Error (Backend "transport budget bypass"))
      ~error:(fun e -> if e = Budget_exhausted then Ok () else Error e)
      (Compiler.compile ~fuel:(artifact.steps - 1) source));
  "transport scalar erasure", (fun () -> same_output
    "(fn (run n u32) (transport (x u32) n n (refl n) (add n 1)))"
    "(fn (run n u32) (add n 1))");
  "transport ghost endpoints and proof", (fun () -> same_output
    "(let (erase n u32) 7 (let (erase p (eq n n)) (refl n) (transport (x u32) n n p 42)))"
    "42");
  "transport symmetry", (fun () -> accepted
    "(let (erase symmetry (pi (erase a u32) (pi (erase b u32) (pi (erase p (eq a b)) (eq b a))))) (fn (erase a u32) (fn (erase b u32) (fn (erase p (eq a b)) (transport (x (eq x a)) a b p (refl a))))) 42)");
  "transport transitivity", (fun () -> accepted
    "(let (erase trans (pi (erase a u32) (pi (erase b u32) (pi (erase c u32) (pi (erase p (eq a b)) (pi (erase q (eq b c)) (eq a c))))))) (fn (erase a u32) (fn (erase b u32) (fn (erase c u32) (fn (erase p (eq a b)) (fn (erase q (eq b c)) (transport (x (eq a x)) b c q p)))))) 42)");
  "transport dependent function family", (fun () -> accepted
    "(fn (run n u32) (let (run f (pi (erase p (eq n n)) u32)) (transport (x (pi (erase p (eq x n)) u32)) n n (refl n) (fn (erase p (eq n n)) 42)) (app erase f (refl n))))");
  "transport product erasure", (fun () -> same_output
    "(fn (run n u32) (snd (transport (x (product bool u32)) n n (refl n) (pair true (add n 1)))))"
    "(fn (run n u32) (snd (pair true (add n 1))))");
  "transport boolean erasure", (fun () -> same_output
    "(if (transport (x bool) 0 0 (refl 0) true) 7 9)"
    "(if true 7 9)");
  "transport reflexive conversion", (fun () -> accepted
    "(let (erase p (eq (transport (x u32) 0 (add 4294967295 1) (refl 0) 42) 42)) (refl 42) 0)");
  "transport computed proof conversion", (fun () -> accepted
    "(let (erase p (eq (transport (x u32) 0 0 (snd (pair 7 (refl 0))) 42) 42)) (refl 42) 0)");
  "transport false proof", (fun () -> kernel_rejects Type_mismatch
    "(transport (x u32) 1 2 (refl 1) 42)");
  "transport proof endpoints", (fun () -> kernel_rejects Type_mismatch
    "(transport (x u32) 1 1 (refl 2) 42)");
  "transport scalar proof", (fun () -> kernel_rejects Type_mismatch
    "(transport (x u32) 1 1 1 42)");
  "transport source type", (fun () -> kernel_rejects Type_mismatch
    "(let (erase p (eq 2 1)) (transport (x (eq x 1)) 2 2 (refl 2) (refl 1)) 0)");
  "transport source uses from endpoint", (fun () -> kernel_rejects Type_mismatch
    "(let (erase f (pi (erase p (eq 1 2)) (eq 2 1))) (fn (erase p (eq 1 2)) (transport (x (eq x 1)) 1 2 p (refl 2))) 0)");
  "transport target uses to endpoint", (fun () -> kernel_rejects Type_mismatch
    "(let (erase f (pi (erase p (eq 1 2)) (eq 1 1))) (fn (erase p (eq 1 2)) (transport (x (eq x 1)) 1 2 p (refl 1))) 0)");
  "transport family formation", (fun () -> kernel_rejects Type_mismatch
    "(transport (x (eq true x)) 1 1 (refl 1) 42)");
  "transport boolean endpoint", (fun () -> kernel_rejects Type_mismatch
    "(transport (x u32) true true (refl 0) 42)");
  "transport target endpoint", (fun () -> kernel_rejects Type_mismatch
    "(transport (x u32) 0 true (refl 0) 42)");
  "transport erased value", (fun () -> kernel_rejects (Erased_use 0)
    "(let (erase n u32) 7 (transport (x u32) n n (refl n) n))");
  "transport runtime proof result", (fun () -> kernel_rejects Runtime_proof
    "(transport (x (eq x x)) 1 1 (refl 1) (refl 1))");
  "transport proof product result", (fun () -> kernel_rejects Runtime_proof
    "(transport (x (product (eq x x) u32)) 1 1 (refl 1) (pair (refl 1) 42))");
  "transport runtime evidence domain", (fun () -> kernel_rejects Runtime_proof
    "(transport (x (pi (run p (eq x x)) u32)) 1 1 (refl 1) (fn (erase p (eq 1 1)) 42))");
  "transport binder scope", (fun () -> rejected (Unknown_name "x")
    "(transport (x u32) x 0 (refl 0) 42)");
  "transport reserved binder", (fun () -> rejected (Parse "binder name is reserved for literals")
    "(transport (true u32) 0 0 (refl 0) 42)");
  "transport substitution under family binder", (fun () -> accepted
    "(app erase (app run (fn (run n u32) (fn (erase p (eq (transport (x u32) n n (refl n) (add n 1)) 8)) 42)) 7) (refl 8))");
  "transport open proof stays symbolic", (fun () -> kernel_rejects Type_mismatch
    "(let (erase f (pi (erase p (eq 0 0)) (eq (transport (x u32) 0 0 p 7) 7))) (fn (erase p (eq 0 0)) (refl 7)) 42)");
  "transport open proof reflexive", (fun () -> accepted
    "(let (erase f (pi (erase p (eq 0 0)) (eq (transport (x u32) 0 0 p 7) (transport (x u32) 0 0 p 7)))) (fn (erase p (eq 0 0)) (refl (transport (x u32) 0 0 p 7))) 42)");
  "boolean conditional composition", (fun () -> accepted
    "(if (if true false true) 1 2)");
  "boolean conditional conversion", (fun () -> accepted
    "(let (erase p (eq (if (if false true (u32-le 5 5)) 7 8) 7)) (refl 7) 0)");
  "boolean conditional substitution", (fun () -> accepted
    "(app erase (app run (fn (run b bool) (fn (erase p (eq (if (if b false true) 7 8) 8)) 0)) true) (refl 8))");
  "boolean conditional mismatch", (fun () -> rejected Type_mismatch "(if true false 0)");
  "boolean conditional export", (fun () -> rejected Unsupported_export "(if true false true)");
  "boolean dead branch erased use", (fun () -> rejected (Erased_use 0)
    "(let (erase b bool) true (if (if true false b) 1 0))");
  "matching product branches", (fun () -> accepted
    "(fst (if true (pair 1 2) (pair 3 4)))");
  "nested product branches", (fun () -> accepted
    "(snd (snd (if false (pair true (pair 1 2)) (pair false (pair 3 4)))))");
  "product branch field mismatch", (fun () -> rejected Type_mismatch
    "(fst (if true (pair 1 true) (pair 2 3)))");
  "product branch shape mismatch", (fun () -> rejected Type_mismatch
    "(fst (if true (pair 1 (pair 2 3)) (pair (pair 1 2) 3)))");
  "conditional function field rejected", (fun () -> rejected Type_mismatch
    "(fst (if true (pair 1 (fn (run x u32) x)) (pair 2 (fn (run x u32) x))))");
  "conditional first function field rejected", (fun () -> rejected Type_mismatch
    "(snd (if true (pair (fn (run x u32) x) 1) (pair (fn (run x u32) x) 2)))");
  "product conditional conversion", (fun () -> accepted
    "(let (erase p (eq (snd (if false (pair 1 2) (pair 3 4))) 4)) (refl 4) 0)");
  "ghost conditional evidence fields rejected", (fun () -> rejected Type_mismatch
    "(let (erase p (product u32 (eq 1 1))) (if true (pair 0 (refl 1)) (pair 0 (refl 1))) 0)");
  "product conditional exact budget", (fun () ->
    let body = "(fn (run x u32) (snd (if (u32-lt x 10) (pair (add x 1) (add x 2)) (pair (add x 3) (add x 4)))))" in
    let source = "(export main " ^ body ^ ")" in
    let* artifact = Compiler.compile source in
    let* exact = Compiler.compile ~fuel:artifact.steps source in
    if exact.wasm <> artifact.wasm then Error (Backend "nondeterministic output")
    else Result.fold ~ok:(fun _ -> Error (Backend "product budget bypass"))
      ~error:(fun e -> if e = Budget_exhausted then Ok () else Error e)
      (Compiler.compile ~fuel:(artifact.steps - 1) source));
  "stuck transport normalizes value", (fun () -> accepted
    "(let (erase f (pi (erase p (eq 0 0)) (eq (transport (x u32) 0 0 p (add 1 2)) (transport (x u32) 0 0 p 3)))) (fn (erase p (eq 0 0)) (refl (transport (x u32) 0 0 p 3))) 42)");
  "strict comparison equal conversion", (fun () -> accepted
    "(let (erase p (eq (if (u32-lt 5 5) 1 2) 2)) (refl 2) 0)");
  "inclusive comparison equal conversion", (fun () -> accepted
    "(let (erase p (eq (if (u32-le 5 5) 1 2) 1)) (refl 1) 0)");
  "pair projections", (fun () -> accepted
    "(let (run p (product u32 bool)) (pair 42 true) (if (snd p) (fst p) 0))");
  "pair export", (fun () -> rejected Unsupported_export "(pair 1 2)");
  "pair parameter export", (fun () -> rejected Unsupported_export
    "(fn (run p (product u32 u32)) (fst p))");
  "scalar fst", (fun () -> rejected Type_mismatch "(fst 1)");
  "scalar snd", (fun () -> rejected Type_mismatch "(snd true)");
  "pair mismatch", (fun () -> rejected Type_mismatch
    "(let (run p (product u32 bool)) (pair true 1) 0)");
  "pair called", (fun () -> rejected Expected_function "(app run (pair 1 2) 0)");
  "pair branch", (fun () -> rejected Type_mismatch "(if true (pair 1 2) 0)");
  "unselected field checked", (fun () -> rejected Type_mismatch "(fst (pair 1 (add true 2)))");
  "unselected erased field", (fun () -> rejected (Erased_use 0)
    "(let (erase x u32) 2 (fst (pair 1 x)))");
  "erased pair use", (fun () -> rejected (Erased_use 0)
    "(let (erase p (product u32 u32)) (pair 1 2) (fst p))");
  "pair runtime proof", (fun () -> rejected Runtime_proof "(fst (pair 1 (refl 2)))");
  "nested runtime proof domain", (fun () -> rejected Runtime_proof
    "(app erase (fn (erase f (pi (run p (product u32 (product u32 (eq 1 1)))) u32)) 0) (fn (run p (product u32 (product u32 (eq 1 1)))) 0))");
  "ghost proof pair", (fun () -> same_output
    "(let (erase p (product u32 (eq 2 2))) (pair 1 (refl 2)) 42)" "42");
  "ghost proof projection", (fun () -> accepted
    "(let (erase p (eq 2 2)) (snd (pair 1 (refl 2))) 42)");
  "pair conversion", (fun () -> accepted
    "(let (erase p (eq (add (fst (pair 3 4)) (snd (pair 5 6))) 9)) (refl 9) 0)");
  "pair conversion mismatch", (fun () -> rejected Type_mismatch
    "(let (erase p (eq (snd (pair 3 4)) 3)) (refl 3) 0)");
  "dependent pair argument substitution", (fun () -> accepted
    "(app erase (app run (fn (run p (product u32 u32)) (fn (erase e (eq (fst p) 7)) (snd p))) (pair 7 42)) (refl 7))");
  "product type index substitution", (fun () -> accepted
    "(app erase (app run (fn (run x u32) (fn (erase p (product (eq x x) (eq x 7))) 42)) 7) (pair (refl 7) (refl 7)))");
  "product type index mismatch", (fun () -> rejected Type_mismatch
    "(app erase (app run (fn (run x u32) (fn (erase p (product (eq x x) (eq x 7))) 42)) 8) (pair (refl 8) (refl 8)))");
  "pair binder capture", (fun () -> accepted
    "(fn (run x u32) (app erase (app run (fn (run p (product u32 u32)) (fn (erase e (eq (fst p) x)) (snd p))) (pair x 42)) (refl x)))");
  "runtime proof in the first product component", (fun () -> rejected Runtime_proof
    "(fn (run p (product (eq 1 1) u32)) 0)");
  "open projections stay distinct", (fun () -> rejected Type_mismatch
    "(app erase (fn (erase f (pi (run p (product u32 u32)) u32)) 0) (fn (run p (product u32 u32)) (app erase (fn (erase e (eq (fst p) (snd p))) 0) (refl (fst p)))))");
  "cross projections stay distinct", (fun () -> rejected Type_mismatch
    "(app erase (fn (erase f (pi (run p (product (product u32 u32) (product u32 u32))) u32)) 0) (fn (run p (product (product u32 u32) (product u32 u32))) (app erase (fn (erase e (eq (fst (snd p)) (snd (fst p)))) 0) (refl (snd (fst p))))))");
  "open projection reflexive", (fun () -> accepted
    "(app erase (fn (erase f (pi (run p (product u32 u32)) u32)) 0) (fn (run p (product u32 u32)) (app erase (fn (erase e (eq (fst p) (fst p))) 0) (refl (fst p)))))");
  "unselected erased field rejected by the kernel", (fun () -> kernel_rejects (Erased_use 0)
    "(let (erase x u32) 2 (fst (pair 1 x)))");
  "pair erasure remapping", (fun () -> same_output
    "(fn (run x u32) (let (erase e (eq x x)) (refl x) (fst (pair x 2))))"
    "(fn (run x u32) (fst (pair x 2)))");
  "boolean let and application", (fun () -> accepted
    "(app run (fn (run b bool) (if b 10 20)) true)");
  "boolean export", (fun () -> rejected Unsupported_export "true");
  "boolean parameter export", (fun () -> rejected Unsupported_export "(fn (run b bool) (if b 1 0))");
  "integer condition", (fun () -> rejected Type_mismatch "(if 1 2 3)");
  "boolean arithmetic", (fun () -> rejected Type_mismatch "(add true 1)");
  "boolean comparison operand", (fun () -> rejected Type_mismatch "(if (u32-eq true 1) 2 3)");
  "boolean equality index", (fun () -> rejected Type_mismatch "(let (erase p (eq true true)) (refl true) 0)");
  "both branches checked", (fun () -> rejected Type_mismatch "(if true 1 false)");
  "function branch rejected", (fun () -> rejected Type_mismatch "(if true (fn (run x u32) x) 0)");
  "erased condition", (fun () -> rejected (Erased_use 0) "(let (erase b bool) true (if b 1 0))");
  "dead branch erased use", (fun () -> rejected (Erased_use 0) "(let (erase x u32) 1 (if true 0 x))");
  "closed branch conversion", (fun () -> accepted
    "(let (erase p (eq (if (u32-lt 2147483648 4294967295) 7 8) 7)) (refl 7) 0)");
  "false branch conversion", (fun () -> accepted
    "(let (erase p (eq (if (u32-le 4294967295 0) 7 8) 8)) (refl 8) 0)");
  "equal branch conversion", (fun () -> accepted
    "(let (erase p (eq (if (u32-eq (add 4294967295 1) 0) 7 8) 7)) (refl 7) 0)");
  "dependent conditional substitution", (fun () -> accepted
    "(app erase (app run (fn (run b bool) (fn (erase p (eq (if b 7 8) 7)) 0)) true) (refl 7))");
  "dependent conditional mismatch", (fun () -> rejected Type_mismatch
    "(app erase (app run (fn (run b bool) (fn (erase p (eq (if b 7 8) 7)) 0)) false) (refl 7))");
  "boolean proof erasure", (fun () -> same_output
    "(fn (run x u32) (let (erase b bool) (u32-lt x 10) (if (u32-le x 20) x 0)))"
    "(fn (run x u32) (if (u32-le x 20) x 0))");
  "parameter limit", (fun () -> Result.map (fun _ -> ()) (emit_parameters 1000));
  "parameter overflow", (fun () -> Result.fold
    ~ok:(fun _ -> Error (Backend "parameter limit bypass"))
    ~error:(fun e -> if e = Backend "function exceeds 1000 parameters" then Ok () else Error e)
    (emit_parameters 1001));
  "reserved binders", (fun () -> List.fold_left (fun acc name ->
    let* () = acc in
    List.fold_left (fun acc body ->
      let* () = acc in
      rejected (Parse "binder name is reserved for literals") body) (Ok ())
      ["(fn (run " ^ name ^ " u32) 42)";
       "(let (erase " ^ name ^ " u32) 1 42)";
       "(fn (run f (pi (run " ^ name ^ " u32) u32)) (app run f 42))"])
    (Ok ()) ["true"; "false"; "5"; "0x2A"; "42x"; "+"; "-x"; "999999999999999999999999"]);
  "symbolic binder", (fun () -> same_output
    "(app run (fn (run tool-price u32) tool-price) 42)"
    "(app run (fn (run x u32) x) 42)");
  "literal", (fun () -> accepted "42");
  "u32 maximum", (fun () -> accepted "4294967295");
  "negative", (fun () -> rejected (Parse "expected an unsigned decimal u32 literal") "-1");
  "overflow literal", (fun () -> rejected (Parse "decimal literal outside u32 range") "4294967296");
  "huge literal", (fun () -> rejected (Parse "decimal literal outside u32 range") "999999999999999999999999");
  "leading zeros", (fun () -> same_output "00000000000000000000000042" "42");
  "alternate literals", (fun () -> List.fold_left (fun acc literal ->
    let* () = acc in
    rejected (Parse "expected an unsigned decimal u32 literal") literal)
    (Ok ()) ["0x2A"; "0o52"; "0b101010"; "1_0"; "+7"; "-0"; "0u42"; "42x"]);
  "unknown name", (fun () -> rejected (Unknown_name "missing") "missing");
  "non-function call", (fun () -> rejected Expected_function "(app run 1 2)");
  "false proof", (fun () -> rejected Type_mismatch "(let (erase p (eq 1 2)) (refl 1) 42)");
  "runtime proof", (fun () -> rejected Runtime_proof "(refl 1)");
  "proof in arithmetic", (fun () -> rejected Runtime_proof "(add (refl 1) 2)");
  "runtime proof binder", (fun () -> rejected Runtime_proof "(fn (run p (eq 1 1)) 42)");
  "erased use", (fun () -> rejected (Erased_use 0) "(let (erase x u32) 42 x)");
  "erased capture", (fun () -> rejected (Erased_use 1)
    "(let (erase x u32) 42 (fn (run y u32) (add x y)))");
  "erased lambda use", (fun () -> rejected (Erased_use 0) "(app erase (fn (erase x u32) x) 42)");
  "relevance mismatch", (fun () -> rejected Type_mismatch "(app erase (fn (run x u32) x) 42)");
  "annotation formation", (fun () -> rejected Expected_function
    "(let (erase p (eq (app run 1 2) 1)) (refl 1) 42)");
  "proof erasure bytes", (fun () -> same_output
    "(fn (run x u32) (let (erase p (eq x x)) (refl x) (add x 1)))"
    "(fn (run x u32) (add x 1))");
  "erased index remapping", (fun () -> same_output
    "(fn (run x u32) (let (erase n u32) 9 (fn (run y u32) (add x y))))"
    "(fn (run x u32) (fn (run y u32) (add x y)))");
  "closed conversion", (fun () -> accepted "(let (erase p (eq (add 20 22) 42)) (refl 42) 7)");
  "modular conversion", (fun () -> accepted "(let (erase p (eq (add 4294967295 1) 0)) (refl 0) 7)");
  "beta conversion", (fun () -> accepted
    "(let (erase p (eq (app run (fn (run x u32) (add x 1)) 41) 42)) (refl 42) 7)");
  "dependent application", (fun () -> accepted (dependent "42" "42" "(refl 42)"));
  "dependent mismatch", (fun () -> rejected Type_mismatch (dependent "41" "42" "(refl 42)"));
  "open dependent substitution", (fun () -> accepted
    ("(fn (run input u32) " ^ dependent "input" "input" "(refl input)" ^ ")"));
  "open dependent mismatch", (fun () -> rejected Type_mismatch
    ("(fn (run input u32) " ^ dependent "input" "0" "(refl 0)" ^ ")"));
  "shadowing", (fun () -> accepted
    "(fn (run x u32) (let (erase x u32) x (fn (run x u32) x)))");
  "higher order", (fun () -> accepted
    "(fn (run x u32) (app run (fn (run f (pi (run n u32) u32)) (app run f x)) (fn (run y u32) (add y 1))))");
  "unsupported export", (fun () -> rejected Unsupported_export
    "(fn (run f (pi (run n u32) u32)) (app run f 1))");
  "zero budget", (fun () -> Result.fold ~ok:(fun _ -> Error (Backend "budget bypass"))
    ~error:(fun e -> if e = Budget_exhausted then Ok () else Error e)
    (Compiler.compile ~fuel:0 "(export main 42)"));
  "budget determinism", (fun () ->
    let source = "(export main (fn (run x u32) (add x 1)))" in
    let* a = Compiler.compile source in
    let* b = Compiler.compile ~fuel:a.steps source in
    if a.wasm <> b.wasm then Error (Backend "nondeterministic output")
    else Result.fold ~ok:(fun _ -> Error (Backend "budget accounting mismatch"))
      ~error:(fun e -> if e = Budget_exhausted then Ok () else Error e)
      (Compiler.compile ~fuel:(a.steps - 1) source));
  "negative AST index", (fun () -> Result.fold ~ok:(fun _ -> Error (Backend "invalid AST accepted"))
    ~error:(fun e -> if e = Invalid_index (-1) then Ok () else Error e)
    (Kernel.check (Budget.create 100) (Ast.Var (-1))));
  "substitution capture", (fun () ->
    let* actual = Ast.subst_term (Budget.create 100) (Ast.Var 0)
      (Ast.Lam (Ast.Runtime, Ast.U32, Ast.Add (Ast.Var 1, Ast.Var 0))) in
    let expected = Ast.Lam (Ast.Runtime, Ast.U32, Ast.Add (Ast.Var 1, Ast.Var 0)) in
    if actual = expected then Ok () else Error (Backend "variable capture"));
]

let () =
  let failures = List.fold_left (fun failures (name, test) ->
    Result.fold ~ok:(fun () -> failures)
      ~error:(fun e -> (name ^ ": " ^ Error.message e) :: failures) (test ())) [] cases in
  List.iter prerr_endline (List.rev failures);
  Printf.printf "kernel: %d cases, %d failures\n" (List.length cases) (List.length failures);
  if failures <> [] then exit 1
