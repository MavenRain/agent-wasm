import { readFile } from 'node:fs/promises';

const [path, ...arguments_] = process.argv.slice(2);
if (!path) {
  console.error('usage: node scripts/run.mjs MODULE.wasm [U32 ...]');
  process.exit(1);
}
try {
  const args = arguments_.map((text) => {
    if (!/^\d+$/.test(text)) throw new Error(`invalid u32: ${text}`);
    const n = Number(text);
    if (!Number.isSafeInteger(n) || n > 0xffffffff) throw new Error(`invalid u32: ${text}`);
    return n;
  });
  const module = await WebAssembly.compile(await readFile(path));
  if (WebAssembly.Module.imports(module).length !== 0) throw new Error('M0 runner accepts no imports');
  const instance = await WebAssembly.instantiate(module, {});
  if (instance.exports.main.length !== args.length) throw new Error('wrong number of arguments');
  console.log(instance.exports.main(...args) >>> 0);
} catch (error) {
  console.error(error.message);
  process.exit(1);
}
