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
    case 'inl': return { side: 'left', value: interpret(tree[2], env) };
    case 'inr': return { side: 'right', value: interpret(tree[2], env) };
    case 'case': {
      const value = interpret(tree[2], env);
      assert(value && (value.side === 'left' || value.side === 'right'), 'reference: invalid sum tag');
      const [name, body] = tree[value.side === 'left' ? 3 : 4];
      return interpret(body, new Map([...env, [name, value.value]]));
    }
    case 'pack': return { kind: 'refinement', value: interpret(tree[2], env), proof: interpret(tree[3], env) };
    case 'value': {
      const packageValue = interpret(tree[1], env);
      assert.equal(packageValue?.kind, 'refinement', 'reference: value requires a refinement');
      return packageValue.value;
    }
    case 'evidence': {
      const packageValue = interpret(tree[1], env);
      assert.equal(packageValue?.kind, 'refinement', 'reference: evidence requires a refinement');
      return packageValue.proof;
    }
    case 'pair': return [interpret(tree[1], env), interpret(tree[2], env)];
    case 'fst': return interpret(tree[1], env)[0];
    case 'snd': return interpret(tree[1], env)[1];
    case 'u32-eq': return interpret(tree[1], env) === interpret(tree[2], env);
    case 'u32-lt': return interpret(tree[1], env) < interpret(tree[2], env);
    case 'u32-le': return interpret(tree[1], env) <= interpret(tree[2], env);
    case 'if': return interpret(tree[interpret(tree[1], env) ? 2 : 3], env);
    case 'add': return (interpret(tree[1], env) + interpret(tree[2], env)) >>> 0;
    case 'fn': return (value) => interpret(tree[2], new Map([...env, [tree[1][1], value]]));
    case 'app': return interpret(tree[2], env)(interpret(tree[3], env));
    case 'let': return interpret(tree[3], new Map([...env, [tree[1][1], interpret(tree[2], env)]]));
    case 'refl': return { witness: interpret(tree[1], env) };
    case 'transport': return interpret(tree[5], env);
    case 'ann': return interpret(tree[1], env);
    default: throw new Error(`reference: unsupported ${tree[0]}`);
  }
}

let seed = 20260906;
const random = (n) => { seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0; return seed % n; };
let fresh = 0;
const refinedU32 = ['refine', ['item', 'u32'], ['eq', 'item', 'item']];
const packU32 = (value) => ['pack', refinedU32, value, ['refl', value]];
function generate(depth, names) {
  if (depth === 0) return random(2) ? names[random(names.length)] : random(0x100000000);
  const name = `v${fresh++}`;
  switch (random(12)) {
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
    case 6: return [random(2) ? 'fst' : 'snd', ['pair',
      generate(depth - 1, names), generate(depth - 1, names)]];
    case 7: return ['case', 'u32', ['if', ['u32-lt', generate(depth - 1, names), 0x80000000],
      ['inl', 'u32', generate(depth - 1, names)], ['inr', 'u32', generate(depth - 1, names)]],
      [name, generate(depth - 1, [...names, name])],
      [name, generate(depth - 1, [...names, name])]];
    case 8: return ['value', packU32(generate(depth - 1, names))];
    case 9: return ['let', ['run', name, refinedU32],
      ['if', ['u32-lt', generate(depth - 1, names), 0x80000000],
        packU32(generate(depth - 1, names)), packU32(generate(depth - 1, names))],
      ['let', ['erase', `proof${fresh++}`, ['eq', ['value', name], ['value', name]]],
        ['evidence', name], ['add', ['value', name], generate(depth - 1, names)]]];
    case 10: {
      const value = generate(depth - 1, names);
      const fields = ['refine', ['fields', ['product', 'bool', 'u32']],
        ['eq', ['snd', 'fields'], ['snd', 'fields']]];
      return ['snd', ['value', ['pack', fields,
        ['pair', ['u32-le', value, 0x80000000], value], ['refl', value]]]];
    }
    case 11: return ['case', 'u32', ['if', ['u32-lt', generate(depth - 1, names), 0x80000000],
      ['inl', refinedU32, packU32(generate(depth - 1, names))],
      ['inr', refinedU32, packU32(generate(depth - 1, names))]],
      [name, ['value', name]], [name, ['add', ['value', name], generate(depth - 1, names)]]];
    default: throw new Error('random generator out of range');
  }
}

const cases = [];
for (const x of [0, 1, 99, 100, 0x7fffffff, 0x80000000, 0xffffffff]) {
  const next = ['add', 'x', 1];
  const indexed = ['refine', ['item', 'u32'], ['eq', 'item', next]];
  cases.push({ name: `refined-increment-${x}`, file: 'examples/refined-increment.aw',
    args: [x], expected: (x + 1) >>> 0 });
  cases.push({ name: `refined-indexed-capture-${x}`, args: [x], body:
    ['fn', ['run', 'x', 'u32'],
      ['let', ['erase', 'outerProof', ['eq', next, next]], ['refl', next],
        ['let', ['run', 'package', indexed], ['pack', indexed, next, 'outerProof'],
          ['let', ['erase', 'checked', ['eq', ['value', 'package'], next]], ['evidence', 'package'],
            ['let', ['run', 'f', ['pi', ['run', 'extra', 'u32'], 'u32']],
              ['fn', ['run', 'extra', 'u32'], ['add', ['value', 'package'], ['add', 'x', 'extra']]],
              ['add', ['app', 'run', 'f', 0], ['app', 'run', 'f', 0xffffffff]]]]]]] });
  cases.push({ name: `refined-closure-argument-${x}`, args: [x], body:
    ['fn', ['run', 'x', 'u32'],
      ['let', ['run', 'f', ['pi', ['run', 'package', refinedU32], 'u32']],
        ['fn', ['run', 'package', refinedU32],
          ['app', 'erase', ['fn', ['erase', 'proof', ['eq', ['value', 'package'], ['value', 'package']]],
            ['add', ['value', 'package'], 'x']], ['evidence', 'package']]],
        ['add', ['app', 'run', 'f', packU32(next)],
          ['app', 'run', 'f', packU32(['add', 'x', 17])]]]] });
  const fields = ['product', refinedU32, ['sum', 'u32', 'bool']];
  const refinedFields = ['refine', ['fields', fields],
    ['eq', ['value', ['fst', 'fields']], ['value', ['fst', 'fields']]]];
  const leftFields = ['pair', packU32(next), ['inl', 'bool', ['add', 'x', 7]]];
  const rightFields = ['pair', packU32(['add', 'x', 3]), ['inr', 'u32', ['u32-eq', 'x', 100]]];
  cases.push({ name: `refined-product-if-${x}`, args: [x], body:
    ['fn', ['run', 'x', 'u32'], ['let', ['run', 'package', refinedFields],
      ['if', ['u32-lt', 'x', 100], ['pack', refinedFields, leftFields, ['refl', next]],
        ['pack', refinedFields, rightFields, ['refl', ['add', 'x', 3]]]],
      ['add', ['value', ['fst', ['value', 'package']]],
        ['case', 'u32', ['snd', ['value', 'package']],
          ['n', ['add', 'n', 'x']], ['flag', ['if', 'flag', 19, 23]]]]]] });
  const rightPayload = ['product', 'bool', refinedU32];
  const refinedSum = ['refine', ['choice', ['sum', refinedU32, rightPayload]], ['eq', 'x', 'x']];
  cases.push({ name: `refined-sum-outer-proof-${x}`, args: [x], body:
    ['fn', ['run', 'x', 'u32'], ['let', ['erase', 'outerProof', ['eq', 'x', 'x']], ['refl', 'x'],
      ['let', ['run', 'package', refinedSum], ['pack', refinedSum,
        ['if', ['u32-lt', 'x', 100], ['inl', rightPayload, packU32(next)],
          ['inr', refinedU32, ['pair', ['u32-eq', 'x', 100], packU32(['add', 'x', 9])]]], 'outerProof'],
        ['let', ['erase', 'checked', ['eq', 'x', 'x']], ['evidence', 'package'],
          ['case', 'u32', ['value', 'package'], ['p', ['value', 'p']],
            ['fields', ['if', ['fst', 'fields'], ['value', ['snd', 'fields']],
              ['add', ['value', ['snd', 'fields']], 'x']]]]]]]] });
  cases.push({ name: `refined-case-result-outer-index-${x}`, args: [x], body:
    ['fn', ['run', 'x', 'u32'], ['let', ['erase', 'outerProof', ['eq', next, next]], ['refl', next],
      ['let', ['run', 'package', indexed],
        ['case', indexed, ['if', ['u32-lt', 'x', 100], ['inl', 'u32', 7], ['inr', 'u32', 11]],
          ['left', ['pack', indexed, next, 'outerProof']],
          ['right', ['let', ['erase', 'branchProof', ['eq', 'right', 'right']], ['refl', 'right'],
            ['pack', indexed, next, 'outerProof']]]],
        ['let', ['erase', 'checked', ['eq', ['value', 'package'], next]], ['evidence', 'package'],
          ['value', 'package']]]]] });
  cases.push({ name: `refined-transport-family-${x}`, args: [x], body:
    ['fn', ['run', 'x', 'u32'], ['let', ['erase', 'outerProof', ['eq', 'x', 'x']], ['refl', 'x'],
      ['value', ['transport', ['index', ['refine', ['item', 'u32'], ['eq', 'item', ['add', 'index', 1]]]],
        'x', 'x', 'outerProof', ['pack', indexed, next, ['refl', next]]]]]] });
  cases.push({ name: `refined-erased-index-capture-${x}`, args: [x], body:
    ['fn', ['run', 'x', 'u32'], ['app', 'run', ['app', 'erase',
      ['fn', ['erase', 'index', 'u32'], ['fn', ['run', 'payload', 'u32'],
        ['let', ['erase', 'proof', ['eq', 'index', 'index']], ['refl', 'index'],
          ['value', ['pack', ['refine', ['item', 'u32'], ['eq', 'index', 'index']], 'payload', 'proof']]]]],
      'x'], next]] });
  cases.push({ name: `refined-erased-package-evidence-${x}`, args: [x], body:
    ['fn', ['run', 'x', 'u32'], ['let', ['erase', 'package', indexed],
      ['pack', indexed, next, ['refl', next]],
      ['let', ['erase', 'proof', ['eq', ['value', 'package'], next]], ['evidence', 'package'],
        next]]] });
  const flag = ['u32-lt', 'x', 100];
  const booleanFamily = ['refine', ['flag', 'bool'],
    ['eq', ['if', 'flag', 1, 0], ['if', 'flag', 1, 0]]];
  cases.push({ name: `refined-boolean-${x}`, args: [x], body:
    ['fn', ['run', 'x', 'u32'], ['if', ['value', ['pack', booleanFamily, flag,
      ['refl', ['if', flag, 1, 0]]]], ['add', 'x', 3], ['add', 'x', 7]]] });
  cases.push({ name: `refined-nested-${x}`, args: [x], body:
    ['fn', ['run', 'x', 'u32'], ['value', ['value', ['pack',
      ['refine', ['inner', refinedU32], ['eq', ['value', 'inner'], ['value', 'inner']]],
      packU32(next), ['refl', next]]]]] });
}
for (const x of [0, 1, 99, 100, 0x7fffffff, 0x80000000, 0xffffffff]) {
  const sum = ['sum', ['product', 'bool', 'u32'], ['sum', 'u32', 'bool']];
  const value = ['if', ['u32-lt', 'x', 100],
    ['inl', ['sum', 'u32', 'bool'], ['pair', ['u32-eq', 'x', 0], ['add', 'x', 7]]],
    ['inr', ['product', 'bool', 'u32'], ['if', ['u32-eq', 'x', 100],
      ['inl', 'bool', ['add', 'x', 9]], ['inr', 'u32', 'true']]]];
  const handler = ['fn', ['run', 's', sum], ['case', 'u32', 's',
    ['p', ['if', ['fst', 'p'], ['snd', 'p'], ['add', ['snd', 'p'], 'x']]],
    ['s', ['case', 'u32', 's', ['n', ['add', 'n', 'x']], ['b', ['if', 'b', 'x', 91]]]]]];
  cases.push({ name: `sum-nested-closure-${x}`, args: [x], body:
    ['fn', ['run', 'x', 'u32'], ['let', ['erase', 'proof', ['eq', 'x', 'x']], ['refl', 'x'],
      ['let', ['run', 'f', ['pi', ['run', 's', sum], 'u32']], handler,
        ['add', ['app', 'run', 'f', value], ['app', 'run', 'f', value]]]]] });
  cases.push({ name: `sum-case-result-${x}`, args: [x], body:
    ['fn', ['run', 'x', 'u32'], ['case', 'u32',
      ['case', ['sum', 'u32', 'bool'], value,
        ['p', ['inl', 'bool', ['snd', 'p']]], ['s', 's']],
      ['n', ['add', 'n', 'x']], ['b', ['if', 'b', 19, 23]]]] });
  cases.push({ name: `sum-case-product-${x}`, args: [x], body:
    ['fn', ['run', 'x', 'u32'], ['snd', ['case', ['product', 'bool', 'u32'], value,
      ['p', 'p'], ['s', ['pair', 'false', ['add', 'x', 11]]]]]] });
  cases.push({ name: `sum-case-boolean-${x}`, args: [x], body:
    ['fn', ['run', 'x', 'u32'], ['if', ['case', 'bool', value,
      ['p', ['fst', 'p']], ['s', ['u32-eq', 'x', 100]]], 17, 29]] });
  cases.push({ name: `sum-shadow-capture-${x}`, args: [x], body:
    ['fn', ['run', 'x', 'u32'], ['case', 'u32', ['inr', 'u32', ['add', 'x', 3]],
      ['x', 'x'], ['y', ['let', ['erase', 'p', ['eq', 'y', 'y']], ['refl', 'y'],
        ['app', 'run', ['fn', ['run', 'z', 'u32'], ['add', 'x', ['add', 'y', 'z']]], 5]]]]] });
}
for (const spent of [0, 1, 99, 0x7fffffff, 0x80000000, 0xffffffff]) {
  for (const proposed of [0, 1, 100, 0x7fffffff, 0x80000000, 0xffffffff]) {
    for (const ceiling of [0, 100, 0xffffffff]) {
      const total = spent + proposed;
      for (const field of [0, 1]) {
        const status = total > 0xffffffff ? 1 : total > ceiling ? 2 : 0;
        cases.push({ name: `budget-sum-${spent}-${proposed}-${ceiling}-${field}`,
          file: 'examples/budget-sum.aw', args: [spent, proposed, ceiling, field],
          expected: field === 0 ? status : status === 0 ? total : 0 });
      }
    }
  }
}
for (const x of [0, 1, 99, 100, 0x80000000, 0xffffffff]) {
  for (const projection of ['fst', 'snd']) {
    cases.push({ name: `product-if-${projection}-${x}`, args: [x], body:
      ['fn', ['run', 'x', 'u32'], ['let', ['erase', 'proof', ['eq', 'x', 'x']], ['refl', 'x'],
        ['let', ['run', 'p', ['product', 'u32', ['product', 'bool', 'u32']]],
          ['if', ['u32-lt', 'x', 100],
            ['let', ['run', 'y', 'u32'], ['add', 'x', 3],
              ['pair', ['add', 'y', 7], ['pair', 'true', ['add', 'y', 11]]]],
            ['if', ['u32-eq', 'x', 100], ['pair', 23, ['pair', 'false', 29]],
              ['pair', ['add', 'x', 17], ['pair', 'true', ['add', 'x', 19]]]]],
          ['add', ['if', ['fst', ['snd', 'p']], ['fst', 'p'], 31],
            projection === 'fst' ? ['fst', 'p'] : ['snd', ['snd', 'p']]]]]]
    });
  }
}
for (const input of [0, 1, 0x7fffffff, 0x80000000, 0xffffffff]) {
  cases.push({ name: `transport-example-${input}`, file: 'examples/transport.aw',
    args: [input], expected: (input + 1) >>> 0 });
  cases.push({ name: `transport-capture-${input}`, body:
    ['fn', ['run', 'input', 'u32'],
      ['let', ['erase', 'proof', ['eq', 'input', 'input']], ['refl', 'input'],
        ['app', 'run', ['transport', ['index', ['pi', ['run', 'arg', 'u32'], 'u32']],
          'input', 'input', 'proof', ['fn', ['run', 'arg', 'u32'], ['add', 'input', 'arg']]], 17]]],
    args: [input] });
  cases.push({ name: `transport-pair-${input}`, body:
    ['fn', ['run', 'input', 'u32'], ['snd', ['transport', ['index', ['product', 'bool', 'u32']],
      'input', 'input', ['refl', 'input'], ['pair', 'true', ['add', 'input', 3]]]]], args: [input] });
}
for (const args of [[7, 100], [9, 0], [7, 101], [8, 50], [9, 0xffffffff]]) {
  cases.push({ name: `tool-policy-${args.join('-')}`, file: 'examples/tool-policy.aw',
    body: ['fn', ['run', 'tool', 'u32'], ['fn', ['run', 'price', 'u32'],
      ['if', ['u32-le', 'price', 100], ['if', ['u32-eq', 'tool', 7], 1,
        ['if', ['u32-eq', 'tool', 9], 1, 0]], 0]]], args });
}
for (const projection of ['fst', 'snd']) {
  cases.push({ name: `pair-${projection}`, body: ['fn', ['run', 'x', 'u32'],
    [projection, ['pair', ['add', 'x', 3], ['add', 'x', 17]]]], args: [20] });
  cases.push({ name: `pair-${projection}-state`, body:
    ['let', ['run', 'p', ['product', 'u32', 'u32']],
      ['pair', ['add', 10, 20], ['add', 30, 40]],
      ['add', [projection, 'p'], ['add', ['fst', 'p'], ['snd', 'p']]]], args: [] });
  cases.push({ name: `pair-${projection}-branch`, body: ['fn', ['run', 'x', 'u32'],
    ['if', ['u32-lt', 'x', 10], [projection, ['pair', ['add', 'x', 1], ['add', 'x', 2]]],
      [projection, ['pair', ['add', 'x', 3], ['add', 'x', 4]]]]], args: [20] });
  cases.push({ name: `pair-${projection}-closure`, body:
    ['app', 'run', [projection, ['pair',
      ['let', ['run', 'x', 'u32'], ['add', 10, 20], ['fn', ['run', 'y', 'u32'], ['add', 'x', 'y']]],
      ['let', ['run', 'x', 'u32'], ['add', 30, 40], ['fn', ['run', 'y', 'u32'], ['add', 'x', 'y']]]]], 5], args: [] });
}
cases.push({ name: 'pair-argument-result', body:
  ['snd', ['app', 'run', ['fn', ['run', 'p', ['product', 'u32', 'u32']],
    ['pair', ['snd', 'p'], ['fst', 'p']]], ['pair', 19, 23]]], args: [] });
cases.push({ name: 'nested-pair', body:
  ['fst', ['snd', ['pair', 1, ['pair', 42, 3]]]], args: [] });
cases.push({ name: 'pair-boolean', body:
  ['let', ['run', 'p', ['product', 'bool', 'u32']], ['pair', ['u32-lt', 1, 2], 42],
    ['if', ['fst', 'p'], ['snd', 'p'], 0]], args: [] });
cases.push({ name: 'pair-before-parameters', body:
  ['snd', ['pair', ['add', 1, 2], ['let', ['run', 'x', 'u32'], ['add', 3, 4],
    ['fn', ['run', 'y', 'u32'], ['add', 'x', 'y']]]]], args: [35] });
for (const op of ['u32-eq', 'u32-lt', 'u32-le']) {
  for (const a of [0, 1, 0x7fffffff, 0x80000000, 0xffffffff]) {
    for (const b of [0, 1, 0x7fffffff, 0x80000000, 0xffffffff]) {
      cases.push({ name: `${op}-${a}-${b}`, body: ['fn', ['run', 'x', 'u32'],
        ['fn', ['run', 'y', 'u32'], ['if', [op, 'x', 'y'], ['add', 'x', 3], ['add', 'y', 7]]]], args: [a, b] });
    }
  }
}
for (const x of [0, 1, 100, 0x80000000, 0xffffffff]) {
  cases.push({ name: `boolean-conditional-${x}`, body:
    ['fn', ['run', 'x', 'u32'], ['let', ['run', 'b', 'bool'],
      ['if', ['u32-lt', 'x', 100], ['u32-eq', ['add', 'x', 1], 2],
        ['if', ['u32-le', 'x', 0x80000000], 'true', 'false']],
      ['add', ['if', 'b', 17, 23], ['if', ['if', 'b', 'false', 'true'], 100, 200]]]], args: [x] });
}
for (const spent of [0, 1, 99, 0x7fffffff, 0x80000000, 0xffffffff]) {
  for (const proposed of [0, 1, 100, 0x7fffffff, 0x80000000, 0xffffffff]) {
    for (const ceiling of [0, 100, 0xffffffff]) {
      // JS addition is exact over two u32 inputs, independently of modular detection.
      cases.push({ name: `budget-policy-${spent}-${proposed}-${ceiling}`,
        file: 'examples/budget-policy.aw',
        args: [spent, proposed, ceiling], expected: Number(spent + proposed <= ceiling) });
      for (const field of [0, 1]) {
        const total = spent + proposed;
        const status = total > 0xffffffff ? 1 : total > ceiling ? 2 : 0;
        cases.push({ name: `budget-result-${spent}-${proposed}-${ceiling}-${field}`,
          file: 'examples/budget-result.aw', args: [spent, proposed, ceiling, field],
          expected: field === 0 ? status : status === 0 ? total : 0 });
      }
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
for (let i = 0; i < 30; i++) {
  const value = generate(4, ['input']);
  const transported = ['transport', ['index', 'u32'], 'input', 'input', ['refl', 'input'], value];
  cases.push({ name: `generated-transport-${i}`, body: ['fn', ['run', 'input', 'u32'],
    ['if', ['u32-lt', 'input', 0x80000000], transported, ['add', transported, 7]]],
    args: [random(0x100000000)] });
}
for (let i = 0; i < 30; i++) {
  const value = generate(4, ['input']);
  const family = ['refine', ['item', 'u32'], ['eq', 'item', value]];
  cases.push({ name: `generated-refinement-${i}`, body: ['fn', ['run', 'input', 'u32'],
    ['let', ['run', 'package', family], ['pack', family, value, ['refl', value]],
      ['let', ['erase', 'proof', ['eq', ['value', 'package'], value]], ['evidence', 'package'],
        ['add', ['value', 'package'], 'input']]]], args: [random(0x100000000)] });
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
cases.push({ name: 'refined-local-limit', body: ['value', packU32(additions(50000, 1))],
  args: [], fuel: '100000000', sameWasm: 'local-limit' });
cases.push({ name: 'sum-case-local-limit', body: ['case', 'u32', ['inr', 'u32', 7],
  ['x', additions(24999, 'x')], ['y', additions(25000, 'y')]], args: [], fuel: '100000000' });
cases.push({ name: 'sum-if-local-limit', body: ['case', 'u32', ['if', 'false',
  ['inl', 'u32', additions(24997, 1)], ['inr', 'u32', additions(24998, 2)]],
  ['x', 'x'], ['y', 'y']], args: [], fuel: '100000000' });
cases.push({ name: 'local-limit-with-parameter', body: ['fn', ['run', 'x', 'u32'],
  additions(49999, 'x')], args: [2], fuel: '100000000' });
cases.push({ name: 'branch-local-limit', body: ['if', ['u32-lt', 1, 2],
  additions(24999, 1), additions(24999, 2)], args: [], fuel: '100000000' });
cases.push({ name: 'product-branch-local-limit', body: ['snd', ['if', 'false',
  ['pair', additions(24998, 1), 7], ['pair', 11, additions(24999, 2)]]],
  args: [], fuel: '100000000' });

try {
  let hostCalls = 0;
  for (const test of cases) {
    const input = join(scratch, `${test.name}.aw`);
    const output = join(scratch, `${test.name}.wasm`);
    writeFileSync(input, test.file ? readFileSync(test.file) : `(export main ${source(test.body)})\n`);
    run(compiler, [...(test.fuel ? ['--fuel', test.fuel] : []), 'compile', input, output]);
    const bytes = readFileSync(output);
    if (test.sameWasm) {
      assert(bytes.equals(readFileSync(join(scratch, `${test.sameWasm}.wasm`))),
        `${test.name}: refinement wrappers altered Wasm bytes`);
    }
    assert(WebAssembly.validate(bytes), `${test.name}: invalid binary`);
    const module = new WebAssembly.Module(bytes);
    assert.deepEqual(WebAssembly.Module.imports(module), [], 'unexpected host authority');
    const { exports } = new WebAssembly.Instance(module, {});
    let expected = test.expected;
    if (expected === undefined) {
      expected = interpret(test.body);
      for (const argument of test.args) expected = expected(argument);
    }
    assert.equal(exports.main(...test.args) >>> 0, expected, `${test.name}: Node/reference`);
    const result = run('wasmtime', ['run', '-C', 'cache=n', '--invoke', 'main', output, ...test.args.map((n) => String(n | 0))]).trim();
    assert.equal(Number(result) >>> 0, expected, `${test.name}: Wasmtime/reference`);
    hostCalls += 2;
  }

  const artifacts = ['increment', 'increment-plain', 'dependent', 'transport'].map((name) => {
    const path = join(scratch, `${name}.wasm`);
    run(compiler, ['compile', `examples/${name}.aw`, path]);
    return readFileSync(path);
  });
  assert(artifacts[0].equals(artifacts[1]), 'proof let altered Wasm bytes');
  assert(artifacts[0].equals(artifacts[2]), 'dependent argument erasure altered Wasm bytes');
  assert(artifacts[0].equals(artifacts[3]), 'transport example altered Wasm bytes');
  assert.equal(run(compiler, ['ir', 'examples/increment.aw']), run(compiler, ['ir', 'examples/increment-plain.aw']));
  assert.equal(run(compiler, ['ir', 'examples/transport.aw']), run(compiler, ['ir', 'examples/increment-plain.aw']));

  const refinedPlain = join(scratch, 'refined-increment-plain.aw');
  writeFileSync(refinedPlain, '(export main (fn (run n u32) (let (run result u32) (add n 1) result)))\n');
  const refinedArtifacts = [refinedPlain, 'examples/refined-increment.aw'].map((file, index) => {
    const path = join(scratch, `refined-erasure-${index}.wasm`);
    run(compiler, ['compile', file, path]);
    return readFileSync(path);
  });
  assert(refinedArtifacts[0].equals(refinedArtifacts[1]), 'refinement evidence altered Wasm bytes');
  assert.equal(run(compiler, ['ir', 'examples/refined-increment.aw']), run(compiler, ['ir', refinedPlain]),
    'refinement evidence altered runtime IR');

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
    ['inl', 'bool', 7], ['inr', 'u32', 'true'],
    ['case', 'u32', 1, ['x', 'x'], ['y', 'y']],
    ['case', 'u32', ['inl', 'bool', 7], ['x', 'x'], ['y', 'y']],
    ['case', 'u32', ['inr', 'u32', 'true'], ['x', 'false'], ['y', 0]],
    ['case', 'u32', ['inl', 'u32', 7], ['x', 'x']],
    ['let', ['erase', 's', ['sum', 'u32', 'u32']], ['inl', 'u32', 7],
      ['case', 'u32', 's', ['x', 'x'], ['y', 'y']]],
    ['transport', ['x', 'u32'], 1, 2, ['refl', 1], 42],
    ['transport', ['x', 'u32'], 1, 1, ['refl', 2], 42],
    ['transport', ['x', 'u32'], 1, 1, ['refl', 1], 'true'],
    ['let', ['erase', 'n', 'u32'], 7, ['transport', ['x', 'u32'], 'n', 'n', ['refl', 'n'], 'n']],
    ['transport', ['x', ['eq', 'x', 'x']], 1, 1, ['refl', 1], ['refl', 1]],
    ['fst', 1], ['pair', 1, 2], ['fst', ['pair', 1, ['refl', 2]]],
    ['let', ['erase', 'p', ['product', 'u32', 'u32']], ['pair', 1, 2], ['snd', 'p']],
    ['let', ['erase', 'b', 'bool'], 'true', ['if', 'b', 1, 0]]]) {
    writeFileSync(malformed, `(export main ${source(body)})`);
    const absent = join(scratch, 'invalid-condition.wasm');
    for (const target of [output, absent]) {
      assert.throws(() => run(compiler, ['compile', malformed, target]));
    }
    assert.equal(readFileSync(output, 'utf8'), 'existing artifact');
    assert(!existsSync(absent));
  }
  const invalidFamily = ['refine', ['item', 'u32'], ['eq', 'true', 'true']];
  const refinementRejections = [
    { name: 'false-proof', body: ['value', ['pack', ['refine', ['item', 'u32'], ['eq', 'item', 0]], 1, ['refl', 1]]] },
    { name: 'wrong-proof', body: ['value', ['pack', refinedU32, 1, ['refl', 2]]] },
    { name: 'wrong-payload', body: ['value', ['pack', refinedU32, 'true', ['refl', 0]]] },
    { name: 'erased-payload', body: ['let', ['erase', 'n', 'u32'], 7, ['value', packU32('n')]] },
    { name: 'erased-package', body: ['let', ['erase', 'package', refinedU32], packU32(7), ['value', 'package']] },
    { name: 'runtime-evidence', body: ['evidence', packU32(7)] },
    { name: 'runtime-evidence-let', body: ['let', ['run', 'proof', ['eq', 7, 7]], ['evidence', packU32(7)], 42] },
    { name: 'value-u32', body: ['value', 7] },
    { name: 'evidence-u32', body: ['let', ['erase', 'proof', ['eq', 7, 7]], ['evidence', 7], 42] },
    { name: 'non-refinement-pack', body: ['value', ['pack', 'u32', 7, ['refl', 7]]] },
    { name: 'non-equality-family', body: ['value', ['pack', ['refine', ['item', 'u32'], 'u32'], 7, 7]] },
    { name: 'proof-payload', body: ['let', ['erase', 'package',
      ['refine', ['item', ['eq', 7, 7]], ['eq', 7, 7]]],
      ['pack', ['refine', ['item', ['eq', 7, 7]], ['eq', 7, 7]], ['refl', 7], ['refl', 7]], 42] },
    { name: 'function-payload', body: ['app', 'run', ['value', ['pack',
      ['refine', ['item', ['pi', ['run', 'n', 'u32'], 'u32']], ['eq', 7, 7]],
      ['fn', ['run', 'n', 'u32'], 'n'], ['refl', 7]]], 42] },
    { name: 'sum-family-formation', body: ['case', 'u32', ['inl', invalidFamily, 7], ['n', 'n'], ['p', 42]] },
    { name: 'sum-nested-family-formation', body: ['case', 'u32',
      ['inr', ['product', 'bool', invalidFamily], 7], ['p', 42], ['n', 'n']] },
    { name: 'case-family-formation', body: ['value', ['case', invalidFamily, ['inl', 'u32', 7],
      ['left', packU32(7)], ['right', packU32(7)]]] },
    { name: 'case-result-binder-scope', body: ['value', ['case',
      ['refine', ['item', 'u32'], ['eq', 'item', 'left']], ['inl', 'u32', 7],
      ['left', packU32(7)], ['right', packU32(7)]]] },
    { name: 'pack-binder-scope-value', body: ['value', ['pack', refinedU32, 'item', ['refl', 7]]] },
    { name: 'pack-binder-scope-proof', body: ['value', ['pack', refinedU32, 7, ['refl', 'item']]] },
    { name: 'refinement-domain-binder-scope', body: ['value', ['pack',
      ['refine', ['item', ['refine', ['inner', 'u32'], ['eq', 'inner', 'item']]], ['eq', 7, 7]],
      packU32(7), ['refl', 7]]] },
    { name: 'refinement-export-result', body: packU32(7) },
    { name: 'refinement-export-argument', body: ['fn', ['run', 'package', refinedU32], ['value', 'package']] },
    { name: 'refinement-binder-arity', body: ['value', ['pack',
      ['refine', ['run', 'item', 'u32'], ['eq', 'item', 'item']], 7, ['refl', 7]]] },
    { name: 'pack-arity', body: ['value', ['pack', refinedU32, 7]] },
    { name: 'value-arity', body: ['value', packU32(7), 0] },
    { name: 'evidence-arity', body: ['let', ['erase', 'proof', ['eq', 7, 7]], ['evidence', packU32(7), 0], 42] },
  ];
  for (const test of refinementRejections) {
    writeFileSync(malformed, `(export main ${source(test.body)})`);
    const absent = join(scratch, 'invalid-refinement.wasm');
    for (const target of [output, absent]) {
      assert.throws(() => run(compiler, ['compile', malformed, target]),
        `refinement ${test.name}: accepted rejected program`);
    }
    assert.equal(readFileSync(output, 'utf8'), 'existing artifact', `refinement ${test.name}: replaced artifact`);
    assert(!existsSync(absent), `refinement ${test.name}: emitted artifact`);
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
      ['transport', [name, 'u32'], 0, 0, ['refl', 0], 42],
      ['value', ['pack', ['refine', [name, 'u32'], ['eq', 7, 7]], 7, ['refl', 7]]],
      ['case', 'u32', ['inl', 'u32', 7], [name, 0], ['y', 'y']],
      ['case', 'u32', ['inl', 'u32', 7], ['x', 'x'], [name, 0]],
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
  for (const body of [additions(50001, 1), ['value', packU32(additions(50001, 1))],
    ['fn', ['run', 'x', 'u32'], additions(50000, 'x')],
    ['case', 'u32', ['inr', 'u32', 7],
      ['x', additions(25000, 'x')], ['y', additions(25000, 'y')]],
    ['case', 'u32', ['if', 'false', ['inl', 'u32', additions(24998, 1)],
      ['inr', 'u32', additions(24998, 2)]], ['x', 'x'], ['y', 'y']],
    ['snd', ['if', 'false', ['pair', additions(24999, 1), 7],
      ['pair', 11, additions(24999, 2)]]],
    ['fst', ['pair', 42, additions(50001, 1)]],
    ['snd', ['pair', additions(25000, 1), additions(25001, 2)]],
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
