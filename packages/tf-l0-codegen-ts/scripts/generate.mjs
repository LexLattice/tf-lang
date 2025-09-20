import { writeFile, mkdir, readFile } from 'node:fs/promises';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { canonicalize } from '../../tf-l0-ir/src/hash.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const runtimeSrcDir = join(here, '..', 'src', 'runtime');
const runtimeFiles = ['inmem.mjs', 'run-ir.mjs'];

export async function generate(ir, { outDir }) {
  await mkdir(join(outDir, 'src'), { recursive: true });
  await writeFile(join(outDir, 'package.json'), JSON.stringify({ name:"tf-generated", private:true, type:"module", scripts:{ start:"node ./dist/pipeline.mjs" }, dependencies:{} }, null, 2) + '\n', 'utf8');
  const adapters = genAdapters(ir); await writeFile(join(outDir,'src','adapters.ts'), adapters, 'utf8');
  const pipeline = genPipeline(ir); await writeFile(join(outDir,'src','pipeline.ts'), pipeline, 'utf8');
  await writeFile(join(outDir,'src','trace.ts'), traceUtil(), 'utf8');
  await writeFile(join(outDir,'src','determinism.ts'), determinismUtil(), 'utf8');
  await writeFile(join(outDir,'src','redaction.ts'), redactionUtil(), 'utf8');
  await emitRunner(ir, outDir);
}
function prims(ir, out=new Set()){ if(!ir||typeof ir!=='object') return out; if(ir.node==='Prim') out.add(ir.prim); for(const c of (ir.children||[])) prims(c,out); return out; }
function genAdapters(ir){ const names=Array.from(prims(ir)); const methods=names.map(n=>`  ${to(n)}(input: any): Promise<any>`).join('\n'); const stubs=names.map(n=>stub(n)).join('\n\n'); return `export interface Adapters {\n${methods}\n}\n\n${stubs}\n`; function to(n){ return 'prim_'+n.replace(/[^a-z0-9]/g,'_'); } function stub(n){ const m=to(n); return `export async function ${m}(input:any):Promise<any>{ throw new Error('Not wired: ${m}'); }`; } }
function genPipeline(ir){ return `import type { Adapters } from './adapters';\nimport { trace } from './trace';\nimport { XorShift32, FixedClock } from './determinism';\nimport type { RedactionPolicy } from './redaction';\n\nexport async function run(adapters: Adapters, input: any, seed: number = 42, clockEpochMs: number = 1690000000000, redaction?: RedactionPolicy): Promise<any> {\n  (globalThis as any).__tf_rng = new XorShift32(seed);\n  (globalThis as any).__tf_clock = new FixedClock(clockEpochMs);\n  (globalThis as any).__tf_redaction = redaction;\n  return await step_${id(ir)}(adapters, input);\n}\n\n${gen(ir)}\n`; function id(node){ return Math.abs(hashCode(JSON.stringify(node))); } function gen(node){ if(node.node==='Prim'){ const m='prim_'+node.prim.replace(/[^a-z0-9]/g,'_'); return `async function step_${id(node)}(adapters: Adapters, input: any){ const span=trace.start('${node.prim}'); const out = await (adapters as any).${m}(input); trace.end(span, input, out, ['TODO-effects']); return out; }`; } if(node.node==='Seq'){ const kids=node.children.map(c=>`acc = await step_${id(c)}(adapters, acc)`).join('\n  '); return `${node.children.map(gen).join('\n\n')}\nasync function step_${id(node)}(adapters: Adapters, input: any){ let acc=input; ${kids}; return acc; }`; } if(node.node==='Par'){ return `${node.children.map(gen).join('\n\n')}\nasync function step_${id(node)}(adapters: Adapters, input: any){ const parts=await Promise.all([${node.children.map(c=>`step_${id(c)}(adapters, input)`).join(', ')}]); return parts; }`; } return `async function step_${id(node)}(){ return null }`; } }
function traceUtil(){ return `import { applyRedaction } from './redaction';\nfunction rng(){ const r=(globalThis as any).__tf_rng; if(!r) throw new Error('rng not initialized'); return r.next(); }\nfunction nowNs(){ const c=(globalThis as any).__tf_clock; if(!c) throw new Error('clock not initialized'); return c.nowNs(); }\nexport const trace = { start(prim){ return { prim, ts: nowNs(), in: null }; }, end(span, input, output, effects){ const evt = { ts_ns: String(span.ts), flow_id: 'flow', run_id: 'run', node_id: span.prim, prim_id: span.prim, span_id: String((rng()*1e9)>>>0), parent_span_id: '', in_hash: hash(input), out_hash: hash(output), effects }; const safe = applyRedaction(evt, (globalThis as any).__tf_redaction); if (process.env.TF_TRACE_STDOUT==='1') console.log(JSON.stringify(safe)); }, }; function hash(v){ return 'sha256:' + require('node:crypto').createHash('sha256').update(JSON.stringify(v)).digest('hex'); }`; }
function determinismUtil(){ return `export { XorShift32, FixedClock } from './determinism';`; }
function redactionUtil(){ return `export type { RedactionPolicy } from './redaction';\nexport { applyRedaction } from './redaction';`; }
function hashCode(s){ let h=0; for(let i=0;i<s.length;i++){ h=((h<<5)-h)+s.charCodeAt(i)|0; } return Math.abs(h); }

async function emitRunner(ir, outDir) {
  const runtimeOut = join(outDir, 'runtime');
  await mkdir(runtimeOut, { recursive: true });
  for (const file of runtimeFiles) {
    const srcPath = join(runtimeSrcDir, file);
    const contents = await readFile(srcPath, 'utf8');
    await writeFile(join(runtimeOut, file), contents, 'utf8');
  }
  const runBundle = genRunBundle(ir);
  await writeFile(join(outDir, 'run.mjs'), runBundle, 'utf8');
}

function genRunBundle(ir) {
  const canonical = canonicalize(ir);
  return `import { mkdir, writeFile } from 'node:fs/promises';\nimport { dirname } from 'node:path';\nimport { fileURLToPath } from 'node:url';\nimport { runIR } from './runtime/run-ir.mjs';\nimport adapters from './runtime/inmem.mjs';\n\nconst ir = ${canonical};\nconst status = await runIR(ir, adapters);\nconst statusUrl = new URL('../../example/run/status.json', import.meta.url);\nconst statusPath = fileURLToPath(statusUrl);\nawait mkdir(dirname(statusPath), { recursive: true });\nawait writeFile(statusPath, JSON.stringify(status) + "\\n", "utf8");\n`;
}
