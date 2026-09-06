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
  "matching product branches rejected", (fun () -> rejected Type_mismatch
    "(fst (if true (pair 1 2) (pair 3 4)))");
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
