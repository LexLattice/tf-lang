import { writeFile, mkdir, copyFile, readFile } from 'node:fs/promises';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

import { canonicalize } from '../../tf-l0-ir/src/hash.mjs';
import { checkIR } from '../../tf-l0-check/src/check.mjs';
import { manifestFromVerdict } from '../../tf-l0-check/src/manifest.mjs';

export async function generate(ir, { outDir }) {
  const moduleDir = dirname(fileURLToPath(import.meta.url));
  const catalogPath = join(moduleDir, '..', '..', 'tf-l0-spec', 'spec', 'catalog.json');
  const catalog = JSON.parse(await readFile(catalogPath, 'utf8'));
  const verdict = checkIR(ir, catalog);
  const manifest = manifestFromVerdict(verdict);

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
      2
    ) + '\n',
    'utf8'
  );

  const adapters = genAdapters(ir);
  await writeFile(join(outDir, 'src', 'adapters.ts'), adapters, 'utf8');

  const pipeline = genPipeline(ir);
  await writeFile(join(outDir, 'src', 'pipeline.ts'), pipeline, 'utf8');

  await writeFile(join(outDir, 'src', 'trace.ts'), traceUtil(), 'utf8');
  await writeFile(join(outDir, 'src', 'determinism.ts'), determinismUtil(), 'utf8');
  await writeFile(join(outDir, 'src', 'redaction.ts'), redactionUtil(), 'utf8');

  await emitRuntime(ir, manifest, outDir);
}

function prims(ir, out = new Set()) {
  if (!ir || typeof ir !== 'object') return out;
  if (ir.node === 'Prim') out.add(ir.prim);
  for (const child of ir.children || []) {
    prims(child, out);
  }
  return out;
}

function genAdapters(ir) {
  const names = Array.from(prims(ir));
  const methodLines = names.map((name) => `  ${to(name)}(input: any): Promise<any>`).join('\n');
  const stubs = names.map((name) => stub(name)).join('\n\n');
  return `export interface Adapters {\n${methodLines}\n}\n\n${stubs}\n`;

  function to(name) {
    return `prim_${name.replace(/[^a-z0-9]/gi, '_')}`;
  }

  function stub(name) {
    const method = to(name);
    return `export async function ${method}(input: any): Promise<any> { throw new Error('Not wired: ${method}'); }`;
  }
}

function genPipeline(ir) {
  return `import type { Adapters } from './adapters';\nimport { trace } from './trace';\nimport { XorShift32, FixedClock } from './determinism';\nimport type { RedactionPolicy } from './redaction';\n\nexport async function run(adapters: Adapters, input: any, seed: number = 42, clockEpochMs: number = 1690000000000, redaction?: RedactionPolicy): Promise<any> {\n  (globalThis as any).__tf_rng = new XorShift32(seed);\n  (globalThis as any).__tf_clock = new FixedClock(clockEpochMs);\n  (globalThis as any).__tf_redaction = redaction;\n  return await step_${id(ir)}(adapters, input);\n}\n\n${gen(ir)}\n`;

  function id(node) {
    return Math.abs(hashCode(JSON.stringify(node)));
  }

  function gen(node) {
    if (node.node === 'Prim') {
      const method = `prim_${node.prim.replace(/[^a-z0-9]/gi, '_')}`;
      return `async function step_${id(node)}(adapters: Adapters, input: any) { const span = trace.start('${node.prim}'); const out = await (adapters as any).${method}(input); trace.end(span, input, out, ['TODO-effects']); return out; }`;
    }
    if (node.node === 'Seq') {
      const body = node.children.map((child) => `acc = await step_${id(child)}(adapters, acc);`).join('\n  ');
      return `${node.children.map(gen).join('\n\n')}\nasync function step_${id(node)}(adapters: Adapters, input: any) { let acc = input; ${body}\n  return acc; }`;
    }
    if (node.node === 'Par') {
      const children = node.children.map((child) => `step_${id(child)}(adapters, input)`).join(', ');
      return `${node.children.map(gen).join('\n\n')}\nasync function step_${id(node)}(adapters: Adapters, input: any) { const parts = await Promise.all([${children}]); return parts; }`;
    }
    return `async function step_${id(node)}() { return null; }`;
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

function hashCode(value) {
  let hash = 0;
  for (let i = 0; i < value.length; i += 1) {
    hash = ((hash << 5) - hash + value.charCodeAt(i)) | 0;
  }
  return Math.abs(hash);
}

async function emitRuntime(ir, manifest, outDir) {
  const moduleDir = dirname(fileURLToPath(import.meta.url));
  const runtimeSrc = join(moduleDir, '..', 'src', 'runtime');
  const runtimeOut = join(outDir, 'runtime');
  await mkdir(runtimeOut, { recursive: true });
  await copyFile(join(runtimeSrc, 'inmem.mjs'), join(runtimeOut, 'inmem.mjs'));
  await copyFile(join(runtimeSrc, 'run-ir.mjs'), join(runtimeOut, 'run-ir.mjs'));
  await copyFile(join(runtimeSrc, 'capabilities.mjs'), join(runtimeOut, 'capabilities.mjs'));

  const canonicalIr = JSON.parse(canonicalize(ir));
  const irLiteral = JSON.stringify(canonicalIr, null, 2);
  const manifestLiteral = canonicalize(manifest);

  const runScript = `import { mkdir, readFile, writeFile } from 'node:fs/promises';\nimport { dirname, join } from 'node:path';\nimport { fileURLToPath } from 'node:url';\nimport { parseArgs } from 'node:util';\nimport { runIR } from './runtime/run-ir.mjs';\nimport { validateCapabilities } from './runtime/capabilities.mjs';\nimport inmem from './runtime/inmem.mjs';\n\nconst MANIFEST = ${manifestLiteral};\nconst ir = ${irLiteral};\n\nconst { values } = parseArgs({\n  options: { caps: { type: 'string' } },\n  allowPositionals: true,\n});\n\nasync function loadCaps() {\n  if (values.caps) {\n    try {\n      const raw = await readFile(values.caps, 'utf8');\n      return JSON.parse(raw);\n    } catch (error) {\n      console.error('tf run.mjs: unable to read --caps file', error);\n      process.exit(1);\n    }\n  }\n  if (process.env.TF_CAPS) {\n    try {\n      return JSON.parse(process.env.TF_CAPS);\n    } catch (error) {\n      console.error('tf run.mjs: unable to parse TF_CAPS env JSON', error);\n      process.exit(1);\n    }\n  }\n  return { effects: [], allow_writes_prefixes: [] };\n}\n\nconst caps = await loadCaps();\nconst validation = validateCapabilities(MANIFEST, caps);\nlet result = { ok: false, ops: 0, effects: [] };\nif (!validation.ok) {\n  console.error(JSON.stringify(validation));\n} else {\n  result = await runIR(ir, inmem);\n}\n\nconst summary = (() => {\n  const effects = Array.isArray(result?.effects) ? Array.from(new Set(result.effects)) : [];\n  effects.sort();\n  return { ok: Boolean(result?.ok), ops: result?.ops ?? 0, effects };\n})();\n\nconsole.log(JSON.stringify(summary));\n\nconst here = dirname(fileURLToPath(import.meta.url));\nconst statusSelf = join(here, 'status.json');\nawait writeFile(statusSelf, JSON.stringify(summary, null, 2) + '\\n', 'utf8');\n\nasync function mergeStatus(targetPath) {\n  try {\n    await mkdir(dirname(targetPath), { recursive: true });\n  } catch {}\n  let merged = summary;\n  try {\n    const existingRaw = await readFile(targetPath, 'utf8');\n    const existing = JSON.parse(existingRaw);\n    const effects = new Set([\n      ...(Array.isArray(existing?.effects) ? existing.effects : []),\n      ...summary.effects,\n    ]);\n    merged = {\n      ok: Boolean(existing?.ok) && Boolean(summary.ok),\n      ops: (existing?.ops ?? 0) + (summary.ops ?? 0),\n      effects: Array.from(effects).sort(),\n    };\n  } catch (err) {\n    if (!err || err.code !== 'ENOENT') {\n      console.warn('tf run.mjs: unable to merge status file', err);\n      return;\n    }\n  }\n  await writeFile(targetPath, JSON.stringify(merged, null, 2) + '\\n', 'utf8');\n}\n\nif (process.env.TF_STATUS_PATH) {\n  await mergeStatus(process.env.TF_STATUS_PATH);\n}\n\nif (!summary.ok) {\n  process.exitCode = 1;\n}\n`;

  await writeFile(join(outDir, 'run.mjs'), runScript, 'utf8');
}
