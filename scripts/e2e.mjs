import { execFileSync } from 'node:child_process';
import { readFileSync, writeFileSync, mkdtempSync, rmSync, existsSync, symlinkSync, linkSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import assert from 'node:assert/strict';

const compiler = resolve('_build/default/bin/main.exe');
const scratch = mkdtempSync(join(tmpdir(), 'agent-wasm-e2e-'));
const run = (file, args) => execFileSync(file, args, { encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
const source = (tree) => Array.isArray(tree) ? `(${tree.map(source).join(' ')})` : String(tree);

// This evaluator uses names and lexical closures. It does not share the
// compiler's de Bruijn substitution, erasure, or Wasm encoding implementation.
function interpret(tree, env = new Map()) {
  if (!Array.isArray(tree)) {
    if (/^\d+$/.test(String(tree))) return Number(tree);
    assert(env.has(tree), `reference: unknown name ${tree}`);
    return env.get(tree);
  }
  switch (tree[0]) {
    case 'add': return (interpret(tree[1], env) + interpret(tree[2], env)) >>> 0;
    case 'fn': return (value) => interpret(tree[2], new Map([...env, [tree[1][1], value]]));
    case 'app': return interpret(tree[2], env)(interpret(tree[3], env));
    case 'let': return interpret(tree[3], new Map([...env, [tree[1][1], interpret(tree[2], env)]]));
    case 'refl': return { witness: interpret(tree[1], env) };
    case 'ann': return interpret(tree[1], env);
    default: throw new Error(`reference: unsupported ${tree[0]}`);
  }
}

let seed = 20260906;
const random = (n) => { seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0; return seed % n; };
let fresh = 0;
function generate(depth, names) {
  if (depth === 0) return random(2) ? names[random(names.length)] : random(0x100000000);
  const name = `v${fresh++}`;
  switch (random(5)) {
    case 0: return ['add', generate(depth - 1, names), generate(depth - 1, names)];
    case 1: return ['let', ['run', name, 'u32'], generate(depth - 1, names), generate(depth - 1, [...names, name])];
    case 2: {
      const index = generate(depth - 1, names);
      return ['let', ['erase', name, ['eq', index, index]], ['refl', index], generate(depth - 1, names)];
    }
    case 3: return ['app', 'run', ['fn', ['run', name, 'u32'], generate(depth - 1, [...names, name])], generate(depth - 1, names)];
    case 4: return names[random(names.length)];
    default: throw new Error('random generator out of range');
  }
}

const cases = [];
for (const n of [0, 1, 63, 64, 127, 128, 8191, 8192, 0x7fffffff, 0x80000000, 0xfffffffe, 0xffffffff]) {
  cases.push({ name: `literal-${n}`, body: n, args: [] });
  cases.push({ name: `add-${n}`, body: ['fn', ['run', 'x', 'u32'], ['add', 'x', n]], args: [0xffffffff] });
}
for (let i = 0; i < 80; i++) {
  cases.push({ name: `generated-${i}`, body: ['fn', ['run', 'input', 'u32'], generate(4, ['input'])], args: [random(0x100000000)] });
}
let wide = 'x';
for (let i = 0; i < 80; i++) wide = ['add', wide, i];
cases.push({ name: 'large-sections', body: ['fn', ['run', 'x', 'u32'], wide], args: [13] });
cases.push({ name: 'capture', body: ['fn', ['run', 'x', 'u32'],
  ['app', 'run', ['app', 'run', ['fn', ['run', 'y', 'u32'],
    ['fn', ['run', 'z', 'u32'], ['add', 'y', 'z']]], 'x'], 2]], args: [40] });
cases.push({ name: 'two-arguments', body: ['fn', ['run', 'x', 'u32'],
  ['fn', ['run', 'y', 'u32'], ['add', 'x', 'y']]], args: [0xffffffff, 2] });

try {
  let hostCalls = 0;
  for (const test of cases) {
    const input = join(scratch, `${test.name}.aw`);
    const output = join(scratch, `${test.name}.wasm`);
    writeFileSync(input, `(export main ${source(test.body)})\n`);
    run(compiler, ['compile', input, output]);
    const bytes = readFileSync(output);
    assert(WebAssembly.validate(bytes), `${test.name}: invalid binary`);
    const module = new WebAssembly.Module(bytes);
    assert.deepEqual(WebAssembly.Module.imports(module), [], 'unexpected host authority');
    const { exports } = new WebAssembly.Instance(module, {});
    let expected = interpret(test.body);
    for (const argument of test.args) expected = expected(argument);
    assert.equal(exports.main(...test.args) >>> 0, expected, `${test.name}: Node/reference`);
    const result = run('wasmtime', ['run', '-C', 'cache=n', '--invoke', 'main', output, ...test.args.map((n) => String(n | 0))]).trim();
    assert.equal(Number(result) >>> 0, expected, `${test.name}: Wasmtime/reference`);
    hostCalls += 2;
  }

  const artifacts = ['increment', 'increment-plain', 'dependent'].map((name) => {
    const path = join(scratch, `${name}.wasm`);
    run(compiler, ['compile', `examples/${name}.aw`, path]);
    return readFileSync(path);
  });
  assert(artifacts[0].equals(artifacts[1]), 'proof let altered Wasm bytes');
  assert(artifacts[0].equals(artifacts[2]), 'dependent argument erasure altered Wasm bytes');
  assert.equal(run(compiler, ['ir', 'examples/increment.aw']), run(compiler, ['ir', 'examples/increment-plain.aw']));

  const output = join(scratch, 'rejected.wasm');
  for (const name of ['reject-false-proof', 'reject-erased-use']) {
    assert.throws(() => run(compiler, ['compile', `examples/${name}.aw`, output]));
    assert(!existsSync(output), 'rejected source emitted output');
  }
  writeFileSync(output, 'existing artifact');
  assert.throws(() => run(compiler, ['compile', 'examples/reject-false-proof.aw', output]));
  assert.equal(readFileSync(output, 'utf8'), 'existing artifact');
  assert.throws(() => run(compiler, ['--fuel', '1', 'compile', 'examples/increment.aw', output]));
  assert.equal(readFileSync(output, 'utf8'), 'existing artifact');
  const malformed = join(scratch, 'malformed.aw');
  for (const text of ['', ')', '(export main 42', '(export main 42) trailing', '('.repeat(130) + ')'.repeat(130), 'x'.repeat(1048577)]) {
    writeFileSync(malformed, text);
    assert.throws(() => run(compiler, ['compile', malformed, output]));
    assert.equal(readFileSync(output, 'utf8'), 'existing artifact');
  }
  const protectedSource = join(scratch, 'protected.aw');
  writeFileSync(protectedSource, '(export main 42)');
  const symlink = join(scratch, 'alias.wasm');
  const hardlink = join(scratch, 'hardlink.wasm');
  symlinkSync(protectedSource, symlink);
  linkSync(protectedSource, hardlink);
  for (const alias of [protectedSource, `${scratch}/./protected.aw`, symlink, hardlink]) {
    assert.throws(() => run(compiler, ['compile', protectedSource, alias]));
    assert.equal(readFileSync(protectedSource, 'utf8'), '(export main 42)');
  }
  assert.throws(() => run(compiler, ['check', join(scratch, 'absent.aw')]));
  assert.throws(() => run(compiler, ['compile', protectedSource, join(scratch, 'absent-dir/out.wasm')]));
  console.log(`e2e: ${cases.length} programs, ${hostCalls} host executions, erasure and rejection checks passed`);
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
