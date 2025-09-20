import { writeFile, mkdir, copyFile, readFile } from 'node:fs/promises';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { canonicalize } from '../../tf-l0-ir/src/hash.mjs';
import { checkIR } from '../../tf-l0-check/src/check.mjs';
import { manifestFromVerdict } from '../../tf-l0-check/src/manifest.mjs';

const moduleDir = dirname(fileURLToPath(import.meta.url));
const runtimeSrc = join(moduleDir, '..', 'src', 'runtime');
const catalogPath = join(moduleDir, '..', '..', 'tf-l0-spec', 'spec', 'catalog.json');

let catalogPromise = null;
async function loadCatalog() {
  if (!catalogPromise) {
    catalogPromise = readFile(catalogPath, 'utf8')
      .then((raw) => JSON.parse(raw))
      .catch(() => ({ primitives: [] }));
  }
  return catalogPromise;
}

export async function generate(ir, { outDir }) {
  await mkdir(join(outDir, 'src'), { recursive: true });
  await writeFile(
    join(outDir, 'package.json'),
    JSON.stringify(
      {
        name: 'tf-generated',
        private: true,
        type: 'module',
        scripts: { start: 'node ./dist/pipeline.mjs' },
        dependencies: {},
      },
      null,
      2,
    ) + '\n',
    'utf8',
  );

  const adapters = genAdapters(ir);
  await writeFile(join(outDir, 'src', 'adapters.ts'), adapters, 'utf8');

  const pipeline = genPipeline(ir);
  await writeFile(join(outDir, 'src', 'pipeline.ts'), pipeline, 'utf8');

  await writeFile(join(outDir, 'src', 'trace.ts'), traceUtil(), 'utf8');
  await writeFile(join(outDir, 'src', 'determinism.ts'), determinismUtil(), 'utf8');
  await writeFile(join(outDir, 'src', 'redaction.ts'), redactionUtil(), 'utf8');

  const catalog = await loadCatalog();
  const verdict = checkIR(ir, catalog);
  const manifest = manifestFromVerdict(verdict);
  await emitRuntime(ir, outDir, manifest);
}

function prims(ir, out = new Set()) {
  if (!ir || typeof ir !== 'object') return out;
  if (ir.node === 'Prim') out.add(ir.prim);
  for (const child of ir.children || []) prims(child, out);
  return out;
}

function genAdapters(ir) {
  const names = Array.from(prims(ir));
  const methods = names.map((name) => `  ${to(name)}(input: any): Promise<any>`).join('\n');
  const stubs = names.map((name) => stub(name)).join('\n\n');
  return `export interface Adapters {\n${methods}\n}\n\n${stubs}\n`;

  function to(name) {
    return `prim_${name.replace(/[^a-z0-9]/g, '_')}`;
  }

  function stub(name) {
    const method = to(name);
    return `export async function ${method}(input:any):Promise<any>{ throw new Error('Not wired: ${method}'); }`;
  }
}

function genPipeline(ir) {
  return `import type { Adapters } from './adapters';\nimport { trace } from './trace';\nimport { XorShift32, FixedClock } from './determinism';\nimport type { RedactionPolicy } from './redaction';\n\nexport async function run(adapters: Adapters, input: any, seed: number = 42, clockEpochMs: number = 1690000000000, redaction?: RedactionPolicy): Promise<any> {\n  (globalThis as any).__tf_rng = new XorShift32(seed);\n  (globalThis as any).__tf_clock = new FixedClock(clockEpochMs);\n  (globalThis as any).__tf_redaction = redaction;\n  return await step_${id(ir)}(adapters, input);\n}\n\n${gen(ir)}\n`;

  function id(node) {
    return Math.abs(hashCode(JSON.stringify(node)));
  }

  function gen(node) {
    if (node.node === 'Prim') {
      const method = `prim_${node.prim.replace(/[^a-z0-9]/g, '_')}`;
      return `async function step_${id(node)}(adapters: Adapters, input: any){ const span=trace.start('${node.prim}'); const out = await (adapters as any).${method}(input); trace.end(span, input, out, ['TODO-effects']); return out; }`;
    }
    if (node.node === 'Seq') {
      const children = node.children.map((child) => `acc = await step_${id(child)}(adapters, acc)`).join('\n  ');
      return `${node.children.map(gen).join('\n\n')}\nasync function step_${id(node)}(adapters: Adapters, input: any){ let acc=input; ${children}; return acc; }`;
    }
    if (node.node === 'Par') {
      const children = node.children.map((child) => `step_${id(child)}(adapters, input)`).join(', ');
      return `${node.children.map(gen).join('\n\n')}\nasync function step_${id(node)}(adapters: Adapters, input: any){ const parts=await Promise.all([${children}]); return parts; }`;
    }
    return `async function step_${id(node)}(){ return null }`;
  }
}

function traceUtil() {
  return `import { applyRedaction } from './redaction';\nfunction rng(){ const r=(globalThis as any).__tf_rng; if(!r) throw new Error('rng not initialized'); return r.next(); }\nfunction nowNs(){ const c=(globalThis as any).__tf_clock; if(!c) throw new Error('clock not initialized'); return c.nowNs(); }\nexport const trace = { start(prim){ return { prim, ts: nowNs(), in: null }; }, end(span, input, output, effects){ const evt = { ts_ns: String(span.ts), flow_id: 'flow', run_id: 'run', node_id: span.prim, prim_id: span.prim, span_id: String((rng()*1e9)>>>0), parent_span_id: '', in_hash: hash(input), out_hash: hash(output), effects }; const safe = applyRedaction(evt, (globalThis as any).__tf_redaction); if (process.env.TF_TRACE_STDOUT==='1') console.log(JSON.stringify(safe)); }, }; function hash(v){ return 'sha256:' + require('node:crypto').createHash('sha256').update(JSON.stringify(v)).digest('hex'); }`;
}

function determinismUtil() {
  return `export { XorShift32, FixedClock } from './determinism';`;
}

function redactionUtil() {
  return `export type { RedactionPolicy } from './redaction';\nexport { applyRedaction } from './redaction';`;
}

function hashCode(s) {
  let h = 0;
  for (let i = 0; i < s.length; i++) {
    h = ((h << 5) - h) + s.charCodeAt(i);
    h |= 0;
  }
  return Math.abs(h);
}

async function emitRuntime(ir, outDir, manifest) {
  const runtimeOut = join(outDir, 'runtime');
  await mkdir(runtimeOut, { recursive: true });
  await copyFile(join(runtimeSrc, 'inmem.mjs'), join(runtimeOut, 'inmem.mjs'));
  await copyFile(join(runtimeSrc, 'run-ir.mjs'), join(runtimeOut, 'run-ir.mjs'));
  await copyFile(join(runtimeSrc, 'capabilities.mjs'), join(runtimeOut, 'capabilities.mjs'));

  const canonicalIr = JSON.parse(canonicalize(ir));
  const irLiteral = JSON.stringify(canonicalIr, null, 2);
  const manifestLiteral = canonicalize(manifest);

  const runScript = `import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { parseArgs } from 'node:util';
import { runIR } from './runtime/run-ir.mjs';
import { validateCapabilities } from './runtime/capabilities.mjs';
import inmem from './runtime/inmem.mjs';

const MANIFEST = ${manifestLiteral};
const ir = ${irLiteral};

function canonicalJson(value) {
  if (Array.isArray(value)) {
    return '[' + value.map(canonicalJson).join(',') + ']';
  }
  if (value && typeof value === 'object') {
    const keys = Object.keys(value).sort();
    return '{' + keys.map((key) => JSON.stringify(key) + ':' + canonicalJson(value[key])).join(',') + '}';
  }
  return JSON.stringify(value);
}

function normalizeCaps(raw) {
  if (!raw || typeof raw !== 'object') {
    return { effects: [], allow_writes_prefixes: [] };
  }
  const effects = Array.isArray(raw.effects) ? raw.effects.filter((v) => typeof v === 'string') : [];
  const allow_writes_prefixes = Array.isArray(raw.allow_writes_prefixes)
    ? raw.allow_writes_prefixes.filter((v) => typeof v === 'string')
    : [];
  return { effects, allow_writes_prefixes };
}

const parsed = parseArgs({
  args: process.argv.slice(2),
  options: {
    caps: { type: 'string' },
  },
  allowPositionals: true,
});

let rawCaps = null;

if (parsed.values.caps) {
  try {
    rawCaps = JSON.parse(await readFile(parsed.values.caps, 'utf8'));
  } catch (err) {
    console.error('tf run.mjs: unable to read capabilities', err?.message ?? err);
  }
} else if (process.env.TF_CAPS) {
  try {
    rawCaps = JSON.parse(process.env.TF_CAPS);
  } catch (err) {
    console.error('tf run.mjs: unable to parse TF_CAPS', err?.message ?? err);
  }
}

const caps = normalizeCaps(rawCaps);
const validation = validateCapabilities(MANIFEST, caps);

let result;
if (!validation.ok) {
  console.error('tf run.mjs: capability check failed', JSON.stringify(validation));
  result = { ok: false, ops: 0, effects: [] };
} else {
  result = await runIR(ir, inmem);
}

const effects = Array.isArray(result?.effects) ? Array.from(new Set(result.effects)) : [];
effects.sort();
const summary = { ok: Boolean(result?.ok), ops: result?.ops ?? 0, effects };

console.log(canonicalJson(summary));

const here = dirname(fileURLToPath(import.meta.url));
const statusSelf = join(here, 'status.json');
await writeFile(statusSelf, JSON.stringify(summary, null, 2) + '\\n', 'utf8');

async function mergeStatus(targetPath) {
  try {
    await mkdir(dirname(targetPath), { recursive: true });
  } catch {}
  let merged = summary;
  try {
    const existingRaw = await readFile(targetPath, 'utf8');
    const existing = JSON.parse(existingRaw);
    const effectsSet = new Set([
      ...(Array.isArray(existing?.effects) ? existing.effects : []),
      ...summary.effects,
    ]);
    merged = {
      ok: Boolean(existing?.ok) && Boolean(summary.ok),
      ops: (existing?.ops ?? 0) + (summary.ops ?? 0),
      effects: Array.from(effectsSet).sort(),
    };
  } catch (err) {
    if (!err || err.code !== 'ENOENT') {
      console.warn('tf run.mjs: unable to merge status file', err);
      return;
    }
  }
  await writeFile(targetPath, JSON.stringify(merged, null, 2) + '\\n', 'utf8');
}

if (process.env.TF_STATUS_PATH) {
  await mergeStatus(process.env.TF_STATUS_PATH);
}
`;

  await writeFile(join(outDir, 'run.mjs'), runScript, 'utf8');
}
