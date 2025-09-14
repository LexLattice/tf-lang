#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

const dir = 'tests/vectors';
let ok = true;
const isPointer = s => typeof s === 'string' && s.startsWith('/');

for (const entry of fs.readdirSync(dir)) {
  const p = path.join(dir, entry);
  const stat = fs.statSync(p);
  if (stat.isDirectory()) continue;            // skip directories like .out
  if (!entry.endsWith('.json')) continue;      // only JSON files

  const v = JSON.parse(fs.readFileSync(p, 'utf8'));

  if (v?.bytecode?.version !== 'L0') {
    console.error(entry, 'version!=L0'); ok=false;
  }

  const instrs = v?.bytecode?.instrs || [];
  for (const ins of instrs) {
    if ((ins.op === 'LENS_PROJ' || ins.op === 'LENS_MERGE') && !isPointer(ins.region)) {
      console.error(entry, 'non-RFC6901 region', ins.region); ok=false;
    }
  }

  const eff = v?.expected?.effect;
  if (!eff || !['read','write','external'].every(k => Array.isArray(eff[k]))) {
    console.error(entry, 'effect missing arrays'); ok=false;
  }
}

if (!ok) process.exit(1);
console.log('vector lint ok');
