#!/usr/bin/env node
/**
 * Breaking change checker (catalog vs baseline).
 * Rules:
 *  - Adding primitives: OK
 *  - Removing primitives: ERROR unless primitive has {deprecated:true} and stays for one release
 *  - Changing primitive id/name/domain/major: ERROR unless major bumped
 *  - For changes in effects/reads/writes/qos: require major bump
 */
import { readFile } from 'node:fs/promises';

function indexById(list){ const m=new Map(); for(const p of list) m.set(p.id, p); return m; }
function sha(x){ return require('node:crypto').createHash('sha256').update(JSON.stringify(x)).digest('hex'); }

const baseIds = JSON.parse(await readFile('contracts/baseline/ids.json','utf8')).primitives || [];
const baseCat = JSON.parse(await readFile('contracts/baseline/catalog.json','utf8')).primitives || [];
const curIds = JSON.parse(await readFile('packages/tf-l0-spec/spec/ids.json','utf8')).primitives || [];
const curCat = JSON.parse(await readFile('packages/tf-l0-spec/spec/catalog.json','utf8')).primitives || [];

const base = indexById(baseCat.length?baseCat:baseIds);
const cur = indexById(curCat.length?curCat:curIds);

const errors=[];
const warnings=[];

for (const [id, pBase] of base) {
  const pCur = cur.get(id);
  if (!pCur) {
    if (pBase.deprecated) warnings.push(`deprecated primitive removed: ${id}`);
    else errors.push(`primitive removed without deprecation: ${id}`);
    continue;
  }
  const fields = ['domain','name','major','effects','reads','writes','qos'];
  for (const f of fields) {
    const a = JSON.stringify(pBase[f]||null);
    const b = JSON.stringify(pCur[f]||null);
    if (a !== b) {
      if (f === 'major') continue; // handled by other fields
      // require major bump for behavior/contract fields
      const bumped = (pCur.major||1) > (pBase.major||1);
      if (!bumped) errors.push(`contract field '${f}' changed for ${id} without major bump`);
    }
  }
}

for (const [id, pCur] of cur) {
  if (!base.has(id)) warnings.push(`new primitive added: ${id}`);
}

if (errors.length) {
  console.error("BREAKING CHANGES DETECTED:");
  for (const e of errors) console.error(" -", e);
  process.exit(1);
} else {
  console.log("No breaking changes. Warnings:");
  for (const w of warnings) console.log(" -", w);
}
