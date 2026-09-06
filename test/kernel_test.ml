open Agent_wasm
open Error

let compile body = Compiler.compile ("(export main " ^ body ^ ")")
let accepted body = Result.map (fun _artifact -> ()) (compile body)
let rejected expected body =
  Result.fold
    ~ok:(fun _artifact -> Error (Backend "unexpected acceptance"))
    ~error:(fun actual -> if actual = expected then Ok () else Error actual)
    (compile body)

let same_output a b =
  let* a = compile a in
  let* b = compile b in
  if a.wasm = b.wasm && a.runtime = b.runtime then Ok ()
  else Error (Backend "erasure changed output")

let dependent n x proof =
  "(app erase (app run (app erase " ^
  "(fn (erase n u32) (fn (run x u32) (fn (erase p (eq x n)) x))) " ^
  n ^ ") " ^ x ^ ") " ^ proof ^ ")"

let cases = [
  "literal", (fun () -> accepted "42");
  "u32 maximum", (fun () -> accepted "4294967295");
  "negative", (fun () -> rejected (Invalid_u32 (-1L)) "-1");
  "overflow literal", (fun () -> rejected (Invalid_u32 4294967296L) "4294967296");
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
