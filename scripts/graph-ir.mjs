#!/usr/bin/env node
/**
 * Emit Graphviz DOT for an IR JSON (stdin or file arg).
 * Usage: node scripts/graph-ir.mjs path/to.ir.json > out.dot
 */
import { readFile } from 'node:fs/promises';

async function load(path){
  if (path) return JSON.parse(await readFile(path,'utf8'));
  const chunks=[]; for await (const c of process.stdin) chunks.push(c);
  return JSON.parse(Buffer.concat(chunks).toString('utf8'));
}
const file = process.argv[2];
const ir = await load(file);

let id=0; const lines=['digraph G {','  node [shape=box,fontname=Arial];'];
function nodeId(){ return 'n'+(++id); }

function walk(n, parent){
  const me = nodeId();
  const label = n.node==='Prim' ? `Prim: ${n.prim}` :
                n.node==='Seq' ? 'Seq' :
                n.node==='Par' ? 'Par' :
                n.node==='Region' ? `Region:${n.kind}` : (n.node||'Unknown');
  lines.push(`  ${me} [label="${label}"];`);
  if (parent) lines.push(`  ${parent} -> ${me};`);
  for (const c of (n.children||[])) walk(c, me);
  return me;
}
walk(ir, null);
lines.push('}');
process.stdout.write(lines.join('\n')+'\n');
