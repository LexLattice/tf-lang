#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import Ajv from 'ajv';
import path from 'node:path';
const OUT_DIR = 'out/0.4/lint'; await mkdir(OUT_DIR, { recursive: true });
const EFFECTS = new Set(["Pure","Time.Read","Time.Wait","Randomness.Read","Network.In","Network.Out","Storage.Read","Storage.Write","Crypto","Policy","Observability"]);
function add(issues, severity, id, message){ issues.push({severity,id,message}); }
const ajv = new Ajv({ strict: true, allErrors: true });
const catalogSchema = JSON.parse(await readFile('schemas/catalog.schema.json','utf8'));
const primitiveSchema = JSON.parse(await readFile('schemas/primitive.schema.json','utf8'));
ajv.addSchema(primitiveSchema, primitiveSchema.$id);
const validate = ajv.compile(catalogSchema);
const cat = JSON.parse(await readFile('packages/tf-l0-spec/spec/catalog.json','utf8'));
const issues = [];
if (!validate(cat)) for (const err of validate.errors||[]) add(issues,'error','schema',ajv.errorsText([err]));
if (!Array.isArray(cat?.primitives)) add(issues,'error','structure','catalog.primitives missing/invalid');
else {
  const seen = new Set();
  for (const p of cat.primitives) {
    if (!p.id) add(issues,'error','id-missing',`missing id: ${p.name??'(unknown)'}`);
    else {
      if (seen.has(p.id)) add(issues,'error','id-duplicate',`duplicate id: ${p.id}`); seen.add(p.id);
      const m = /^tf:([a-z0-9\-]+)\/([a-z0-9\-]+)@(\d+)$/.exec(p.id);
      if (!m) add(issues,'error','id-format',`bad id ${p.id}`);
      else if (p.domain && p.domain!==m[1]) add(issues,'error','domain-mismatch',`id domain ${m[1]} != property domain ${p.domain} (${p.id})`);
    }
    const eff = Array.isArray(p.effects)?p.effects:[];
    for (const e of eff) if (!EFFECTS.has(e)) add(issues,'warn','effect-unknown',`unknown effect '${e}' on ${p.id}`);
    if (eff.includes('Storage.Read')) {
      if (!Array.isArray(p.reads)||p.reads.length===0) add(issues,'error','reads-missing',`Storage.Read requires 'reads' on ${p.id}`);
      else for (const r of p.reads) if (!r.uri) add(issues,'error','reads-uri-missing',`reads entry missing uri on ${p.id}`);
    }
    if (eff.includes('Storage.Write')) {
      if (!Array.isArray(p.writes)||p.writes.length===0) add(issues,'error','writes-missing',`Storage.Write requires 'writes' on ${p.id}`);
      else for (const r of p.writes) if (!r.uri) add(issues,'error','writes-uri-missing',`writes entry missing uri on ${p.id}`);
    }
    if (eff.includes('Network.In')||eff.includes('Network.Out')) {
      if (!p.qos || !p.qos.delivery_guarantee) add(issues,'error','qos-delivery-missing',`Network.* requires qos.delivery_guarantee on ${p.id}`);
    }
    if ((p.name||'').match(/encrypt|decrypt|sign|verify|secret/)) {
      if (!Array.isArray(p.data_classes)||p.data_classes.length===0) add(issues,'warn','data-classes-missing',`Consider data_classes for crypto/secret op ${p.id}`);
    }
    if (eff.includes('Pure') && ((p.reads&&p.reads.length)||(p.writes&&p.writes.length))) {
      add(issues,'warn','pure-footprints',`Pure primitive declares reads/writes on ${p.id}`);
    }
  }
}
const summary={errors:issues.filter(i=>i.severity==='error').length,warnings:issues.filter(i=>i.severity==='warn').length};
await writeFile(path.join(OUT_DIR,'report.json'),JSON.stringify({issues,summary},null,2)+'\n','utf8');
await writeFile(path.join(OUT_DIR,'summary.txt'),`errors=${summary.errors}\nwarnings=${summary.warnings}\n`,'utf8');
if (summary.errors>0){ console.error(`LINT FAILED: ${summary.errors} error(s), ${summary.warnings} warning(s).`); process.exit(1);} else { console.log(`Lint OK: ${summary.errors} error(s), ${summary.warnings} warning(s).`);}
