import { writeFile, mkdir } from 'node:fs/promises';
import { join } from 'node:path';

export async function generate(ir, { outDir }) {
  await mkdir(join(outDir, 'src'), { recursive: true });
  await writeFile(join(outDir, 'package.json'), JSON.stringify({
    name: "tf-generated",
    private: true,
    type: "module",
    scripts: { start: "node ./dist/pipeline.mjs" },
    dependencies: {}
  }, null, 2) + '\n', 'utf8');

  const adapters = genAdapters(ir);
  await writeFile(join(outDir, 'src', 'adapters.ts'), adapters, 'utf8');
  const pipeline = genPipeline(ir);
  await writeFile(join(outDir, 'src', 'pipeline.ts'), pipeline, 'utf8');
  await writeFile(join(outDir, 'src', 'trace.ts'), traceUtil(), 'utf8');
}

function prims(ir, out=new Set()) {
  if (!ir || typeof ir !== 'object') return out;
  if (ir.node==='Prim') out.add(ir.prim);
  for (const c of (ir.children||[])) prims(c, out);
  return out;
}

function genAdapters(ir) {
  const names = Array.from(prims(ir));
  const methods = names.map(n=>`  ${toMethod(n)}(input: any): Promise<any>`).join('\n');
  const stubs = names.map(n=>textStub(n)).join('\n\n');
  return `export interface Adapters {\n${methods}\n}\n\n${stubs}\n`;
  function toMethod(n){ return 'prim_' + n.replace(/[^a-z0-9]/g,'_'); }
  function textStub(n){
    const m = toMethod(n);
    return `export async function ${m}(input: any): Promise<any> {\n  throw new Error('Not wired: ${m}');\n}`;
  }
}

function genPipeline(ir) {
  return `import type { Adapters } from './adapters';\nimport { trace } from './trace';\n\nexport async function run(adapters: Adapters, input: any): Promise<any> {\n  return await step_${id(ir)}(adapters, input);\n}\n\n${gen(ir)}\n`;
  function id(node){ return Math.abs(hashCode(JSON.stringify(node))); }
  function gen(node){
    if (node.node==='Prim') {
      const m = 'prim_' + node.prim.replace(/[^a-z0-9]/g,'_');
      return `async function step_${id(node)}(adapters: Adapters, input: any){\n  const span=trace.start('${node.prim}');\n  const out = await (adapters as any).${m}(input);\n  trace.end(span, input, out, ['TODO-effects']);\n  return out;\n}`;
    }
    if (node.node==='Seq') {
      const kids = node.children.map(c=>`await step_${id(c)}(adapters, acc)`).join('\n  ');
      return `${node.children.map(gen).join('\n\n')}\nasync function step_${id(node)}(adapters: Adapters, input: any){\n  let acc = input;\n  ${kids};\n  return acc;\n}`;
    }
    if (node.node==='Par') {
      return `${node.children.map(gen).join('\n\n')}\nasync function step_${id(node)}(adapters: Adapters, input: any){\n  const parts = await Promise.all([${node.children.map(c=>`step_${id(c)}(adapters, input)`).join(', ')}]);\n  return parts;\n}`;
    }
    return `async function step_${id(node)}(){ return null }`;
  }
}

function traceUtil(){
  return `export const trace = {\n  start(prim){ return { prim, ts: Date.now()*1_000_000, in: null }; },\n  end(span, input, output, effects){ const evt = { ts_ns: String(span.ts), flow_id: 'flow', run_id: 'run', node_id: span.prim, prim_id: span.prim, span_id: String(Math.random()).slice(2), parent_span_id: '', in_hash: hash(input), out_hash: hash(output), effects }; if (process.env.TF_TRACE_STDOUT==='1') console.log(JSON.stringify(evt)); },\n};\nfunction hash(v){ return 'sha256:' + require('node:crypto').createHash('sha256').update(JSON.stringify(v)).digest('hex'); }`;
}

function hashCode(s){ let h=0; for(let i=0;i<s.length;i++){ h=((h<<5)-h)+s.charCodeAt(i)|0; } return h; }
