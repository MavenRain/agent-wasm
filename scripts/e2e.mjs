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
    if (tree === 'true') return true;
    if (tree === 'false') return false;
    if (/^\d+$/.test(String(tree))) return Number(tree);
    assert(env.has(tree), `reference: unknown name ${tree}`);
    return env.get(tree);
  }
  switch (tree[0]) {
    case 'u32-eq': return interpret(tree[1], env) === interpret(tree[2], env);
    case 'u32-lt': return interpret(tree[1], env) < interpret(tree[2], env);
    case 'u32-le': return interpret(tree[1], env) <= interpret(tree[2], env);
    case 'if': return interpret(tree[interpret(tree[1], env) ? 2 : 3], env);
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
  switch (random(6)) {
    case 0: return ['add', generate(depth - 1, names), generate(depth - 1, names)];
    case 1: return ['let', ['run', name, 'u32'], generate(depth - 1, names), generate(depth - 1, [...names, name])];
    case 2: {
      const index = generate(depth - 1, names);
      return ['let', ['erase', name, ['eq', index, index]], ['refl', index], generate(depth - 1, names)];
    }
    case 3: return ['app', 'run', ['fn', ['run', name, 'u32'], generate(depth - 1, [...names, name])], generate(depth - 1, names)];
    case 4: return names[random(names.length)];
    case 5: return ['if', [['u32-eq', 'u32-lt', 'u32-le'][random(3)],
      generate(depth - 1, names), generate(depth - 1, names)],
      generate(depth - 1, names), generate(depth - 1, names)];
    default: throw new Error('random generator out of range');
  }
}

const cases = [];
for (const op of ['u32-eq', 'u32-lt', 'u32-le']) {
  for (const a of [0, 1, 0x7fffffff, 0x80000000, 0xffffffff]) {
    for (const b of [0, 1, 0x7fffffff, 0x80000000, 0xffffffff]) {
      cases.push({ name: `${op}-${a}-${b}`, body: ['fn', ['run', 'x', 'u32'],
        ['fn', ['run', 'y', 'u32'], ['if', [op, 'x', 'y'], ['add', 'x', 3], ['add', 'y', 7]]]], args: [a, b] });
    }
  }
}
for (const flag of ['true', 'false']) {
  cases.push({ name: `boolean-closure-${flag}`, body:
    ['app', 'run', ['fn', ['run', 'b', 'bool'],
      ['let', ['run', 'x', 'u32'], ['if', 'b', ['add', 10, 1], ['add', 20, 2]],
        ['add', 'x', ['if', 'b', ['add', 'x', 3], ['add', 'x', 4]]]]], flag], args: [] });
}
for (const price of [0, 99, 100, 101, 0xffffffff]) {
  cases.push({ name: `price-ceiling-${price}`, body: ['fn', ['run', 'price', 'u32'],
    ['if', ['u32-le', 'price', 100], 1, 0]], args: [price] });
}
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
for (const selected of ['x', 'y', 'z']) {
  cases.push({ name: `select-${selected}`, body: ['fn', ['run', 'x', 'u32'],
    ['fn', ['run', 'y', 'u32'], ['fn', ['run', 'z', 'u32'], selected]]],
    args: [11, 22, 33] });
  cases.push({ name: `erased-select-${selected}`, body: ['fn', ['run', 'x', 'u32'],
    ['let', ['erase', 'p', ['eq', 'x', 'x']], ['refl', 'x'],
      ['fn', ['run', 'y', 'u32'], ['fn', ['run', 'z', 'u32'], selected]]]],
    args: [11, 22, 33] });
}
cases.push({ name: 'leading-zeros', body: '00000000000000000000000042', args: [] });
cases.push({ name: 'state-through-call', body:
  ['app', 'run', ['let', ['run', 'captured', 'u32'], ['add', 10, 20],
    ['fn', ['run', 'arg', 'u32'], ['add', 'captured', 'arg']]], ['add', 3, 4]], args: [] });
cases.push({ name: 'state-before-parameters', body:
  ['let', ['run', 'captured', 'u32'], ['add', 10, 20],
    ['fn', ['run', 'arg', 'u32'], ['add', 'captured', 'arg']]], args: [12] });

// Balanced trees reach the backend limit without exceeding parser depth.
function additions(count, leaf) {
  if (count === 0) return leaf;
  const left = Math.floor((count - 1) / 2);
  return ['add', additions(left, leaf), additions(count - 1 - left, leaf)];
}
cases.push({ name: 'local-limit', body: additions(50000, 1), args: [], fuel: '100000000' });
cases.push({ name: 'local-limit-with-parameter', body: ['fn', ['run', 'x', 'u32'],
  additions(49999, 'x')], args: [2], fuel: '100000000' });
cases.push({ name: 'branch-local-limit', body: ['if', ['u32-lt', 1, 2],
  additions(24999, 1), additions(24999, 2)], args: [], fuel: '100000000' });

try {
  let hostCalls = 0;
  for (const test of cases) {
    const input = join(scratch, `${test.name}.aw`);
    const output = join(scratch, `${test.name}.wasm`);
    writeFileSync(input, `(export main ${source(test.body)})\n`);
    run(compiler, [...(test.fuel ? ['--fuel', test.fuel] : []), 'compile', input, output]);
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
  for (const body of [['if', 1, 2, 3], ['if', 'true', 1, 'false'],
    ['let', ['erase', 'b', 'bool'], 'true', ['if', 'b', 1, 0]]]) {
    writeFileSync(malformed, `(export main ${source(body)})`);
    const absent = join(scratch, 'invalid-condition.wasm');
    for (const target of [output, absent]) {
      assert.throws(() => run(compiler, ['compile', malformed, target]));
    }
    assert.equal(readFileSync(output, 'utf8'), 'existing artifact');
    assert(!existsSync(absent));
  }
  for (const text of ['', ')', '(export main 42', '(export main 42) trailing', '('.repeat(130) + ')'.repeat(130), 'x'.repeat(1048577)]) {
    writeFileSync(malformed, text);
    assert.throws(() => run(compiler, ['compile', malformed, output]));
    assert.equal(readFileSync(output, 'utf8'), 'existing artifact');
  }
  for (const literal of ['0x2A', '0o52', '0b101010', '1_0', '+7', '-0', '-1', '0u42', '42x',
    '4294967296', '999999999999999999999999']) {
    writeFileSync(malformed, `(export main ${literal})`);
    assert.throws(() => run(compiler, ['compile', malformed, output]), /parse:/);
    assert.equal(readFileSync(output, 'utf8'), 'existing artifact');
  }
  for (const name of ['true', 'false', '5', '0x2A', '42x', '+', '-x']) {
    for (const body of [
      ['fn', ['run', name, 'u32'], 42],
      ['let', ['erase', name, 'u32'], 1, 42],
      ['fn', ['run', 'f', ['pi', ['run', name, 'u32'], 'u32']], ['app', 'run', 'f', 42]],
    ]) {
      writeFileSync(malformed, `(export main ${source(body)})`);
      const absent = join(scratch, 'bad-binder.wasm');
      for (const target of [output, absent]) {
        assert.throws(() => run(compiler, ['compile', malformed, target]),
          /parse: binder name is reserved for literals/);
      }
      assert.equal(readFileSync(output, 'utf8'), 'existing artifact');
      assert(!existsSync(absent));
    }
  }
  for (const body of [additions(50001, 1), ['fn', ['run', 'x', 'u32'], additions(50000, 'x')],
    additions(65535, 1), ['if', ['u32-lt', 1, 2], additions(25000, 1), additions(24999, 2)]]) {
    writeFileSync(malformed, `(export main ${source(body)})`);
    for (const target of [output, join(scratch, 'over-limit.wasm')]) {
      assert.throws(() => run(compiler, ['--fuel', '100000000', 'compile', malformed, target]),
        /backend: function exceeds 50000 parameters and locals/);
    }
    assert.equal(readFileSync(output, 'utf8'), 'existing artifact');
    assert(!existsSync(join(scratch, 'over-limit.wasm')));
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
