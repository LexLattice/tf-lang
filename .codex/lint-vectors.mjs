#!/usr/bin/env node
import fs from 'node:fs';
const dir = 'tests/vectors';
let ok = true;
for (const f of fs.readdirSync(dir)) {
    const v = JSON.parse(fs.readFileSync(`${dir}/${f}`, 'utf8'));
    if (v.bytecode?.version !== 'L0') { console.error(f, 'version!=L0'); ok = false; }
    const instrs = v.bytecode?.instrs || [];
    for (const ins of instrs) {
        if (ins.op?.startsWith('LENS_') && typeof ins.region === 'string' && !ins.region.startsWith('/')) {
            console.error(f, 'non-RFC6901 region', ins.region); ok = false;
        }
    }
    // tiny effect sorter hint
    const eff = v.expected?.effect;
    if (eff) ['read', 'write', 'external'].forEach(k => {
        if (!Array.isArray(eff[k])) { console.error(f, 'effect missing array', k); ok = false; }
    });
}
if (!ok) process.exit(1);
console.log('vector lint ok');
