#!/usr/bin/env node
/**
 * Emit Graphviz DOT for an IR JSON.
 * Usage:
 *   node scripts/graph-ir.mjs <input.ir.json> [output.dot]
 * If output.dot is provided, the script will create parent dirs and write to it.
 */
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import path from 'node:path';

async function load(p) {
  if (p) return JSON.parse(await readFile(p, 'utf8'));
  const chunks = [];
  for await (const c of process.stdin) chunks.push(c);
  return JSON.parse(Buffer.concat(chunks).toString('utf8'));
}

const inPath = process.argv[2];
const outPath = process.argv[3];

if (!inPath) {
  console.error('Usage: node scripts/graph-ir.mjs <input.ir.json> [output.dot]');
  process.exit(2);
}

const ir = await load(inPath);

let id = 0;
const lines = ['digraph G {', '  node [shape=box,fontname=Arial];'];
function nodeId() { return 'n' + (++id); }

function walk(n, parent) {
  const me = nodeId();
  const label =
    n.node === 'Prim' ? `Prim: ${n.prim}` :
      n.node === 'Seq' ? 'Seq' :
        n.node === 'Par' ? 'Par' :
          n.node === 'Region' ? `Region:${n.kind}` :
            (n.node || 'Unknown');
  lines.push(`  ${me} [label="${label}"];`);
  if (parent) lines.push(`  ${parent} -> ${me};`);
  for (const c of (n.children || [])) walk(c, me);
}
walk(ir, null);
lines.push('}');

const dot = lines.join('\n') + '\n';

if (outPath) {
  await mkdir(path.dirname(outPath), { recursive: true });
  await writeFile(outPath, dot, 'utf8');
} else {
  process.stdout.write(dot);
}
