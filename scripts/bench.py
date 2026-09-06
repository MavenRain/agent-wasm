"""Informational compilation microbenchmark, not a language-wide speed gate."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import statistics
import subprocess
import time


def command(args, cwd=None):
    return subprocess.run(args, cwd=cwd, check=True, capture_output=True, text=True).stdout.strip()


def balanced(leaves, combine):
    while len(leaves) > 1:
        leaves = [combine(leaves[i], leaves[i + 1]) if i + 1 < len(leaves) else leaves[i]
                  for i in range(0, len(leaves), 2)]
    return leaves[0]


def measure(action, samples):
    action()
    timings = []
    for _ in range(samples):
        start = time.perf_counter_ns()
        action()
        timings.append((time.perf_counter_ns() - start) / 1_000_000)
    return {"median_ms": statistics.median(timings), "samples_ms": timings}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=7)
    args = parser.parse_args()
    if args.samples < 3:
        parser.error("at least three samples are required")
    root = Path(__file__).resolve().parent.parent
    compiler = root / "_build/default/bin/main.exe"
    ocamlopt = shutil.which("ocamlopt")
    if not ocamlopt:
        parser.error("ocamlopt is missing; run through opam exec")
    out = root / "artifacts/bench"
    out.mkdir(parents=True, exist_ok=True)
    results = {
        "status": "informational; no OCaml-speed acceptance claim",
        "method": "fresh compiler processes and fresh outputs; one warmup; warm OS caches; no linking or host JIT timing",
        "comparison": "core Wasm module emission versus OCaml native object emission; different backends",
        "platform": platform.platform(),
        "machine": platform.machine(),
        "cpu_count": os.cpu_count(),
        "ocamlopt": command([ocamlopt, "-version"]),
        "compiler_sha256": hashlib.sha256(compiler.read_bytes()).hexdigest(),
        "corpora": [],
    }
    for size in (32, 256, 1024):
        case = out / str(size)
        case.mkdir(exist_ok=True)
        plain_leaves = [f"(add x {i})" for i in range(size)]
        proof_leaves = [f"(let (erase p{i} (eq x x)) (refl x) (add x {i}))" for i in range(size)]
        transport_leaves = [f"(transport (index u32) x x (refl x) (add x {i}))" for i in range(size)]
        paths = {}
        for name, leaves in (("plain", plain_leaves), ("proof", proof_leaves), ("transport", transport_leaves)):
            body = balanced(leaves, lambda a, b: f"(add\n{a}\n{b})")
            paths[name] = case / f"{name}.aw"
            paths[name].write_text(f"(export main (fn (run x u32) {body}))\n")
        ml = case / "baseline.ml"
        ml_body = balanced([f"(Int32.add x {i}l)" for i in range(size)], lambda a, b: f"(Int32.add\n{a}\n{b})")
        ml.write_text(f"let main (x : int32) : int32 = {ml_body}\n")
        row = {"leaves": size, "runtime_additions": size * 2 - 1,
               "source_sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in [*paths.values(), ml]}}
        for name, path in paths.items():
            output = case / f"{name}.wasm"

            def compile_aw(path=path, output=output):
                output.unlink(missing_ok=True)
                return command([str(compiler), "compile", str(path), str(output)])

            row[name] = measure(compile_aw, args.samples)
            row[name]["source_bytes"] = path.stat().st_size
            row[name]["wasm_bytes"] = output.stat().st_size
        for name in ("proof", "transport"):
            if (case / "plain.wasm").read_bytes() != (case / f"{name}.wasm").read_bytes():
                raise RuntimeError(f"{name} corpus changed runtime output")

        def compile_ml():
            for extension in ("cmi", "cmx", "o"):
                (case / f"baseline.{extension}").unlink(missing_ok=True)
            command([ocamlopt, "-c", "baseline.ml"], cwd=case)

        row["ocaml"] = measure(compile_ml, args.samples)
        row["ocaml"]["source_bytes"] = ml.stat().st_size
        for name in ("plain", "proof", "transport"):
            row[name]["ratio_to_ocaml"] = row[name]["median_ms"] / row["ocaml"]["median_ms"]

        # Independently execute every generated program outside the timed region.
        check = case / "check.ml"
        check.write_text('let () = Printf.printf "%ld\\n" (Baseline.main 123l)\n')
        command([ocamlopt, "-o", "baseline-run", "baseline.cmx", "check.ml"], cwd=case)
        ocaml_value = int(command([str(case / "baseline-run")])) & 0xffffffff
        expected = (size * 123 + size * (size - 1) // 2) & 0xffffffff
        if ocaml_value != expected:
            raise RuntimeError("benchmark programs disagree")
        for name in paths:
            wasm_value = int(command(["node", str(root / "scripts/run.mjs"), str(case / f"{name}.wasm"), "123"]))
            if wasm_value != expected:
                raise RuntimeError(f"{name} benchmark program disagrees")
        results["corpora"].append(row)
        print(f"{size} leaves: plain {row['plain']['median_ms']:.3f} ms, "
              f"proof {row['proof']['median_ms']:.3f} ms, "
              f"transport {row['transport']['median_ms']:.3f} ms, OCaml {row['ocaml']['median_ms']:.3f} ms")
    (out / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    print(f"Informational results: {out / 'results.json'}")


if __name__ == "__main__":
    main()
