#!/usr/bin/env node
/**
 * Catalog linter with severity levels.
 */
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import Ajv from 'ajv/dist/2020.js';
import path from 'node:path';

const OUT_DIR = 'out/0.4/lint';
await mkdir(OUT_DIR, { recursive: true });

const EFFECT_FAMILIES = new Set([
  'Pure', 'Time.Read', 'Time.Wait', 'Randomness.Read',
  'Network.In', 'Network.Out', 'Storage.Read', 'Storage.Write',
  'Crypto', 'Policy', 'Observability'
]);

function addIssue(issues, severity, id, message) {
  issues.push({ severity, id, message });
}

// Ajv + schemas (register $refs first)
const ajv = new Ajv({ strict: true, allErrors: true });
const catalogSchema = JSON.parse(await readFile('schemas/catalog.schema.json', 'utf8'));
const primitiveSchema = JSON.parse(await readFile('schemas/primitive.schema.json', 'utf8'));
const footprintSchema = JSON.parse(await readFile('schemas/footprint-pattern.schema.json', 'utf8'));
const errorTaxSchema = JSON.parse(await readFile('schemas/error-taxonomy.schema.json', 'utf8'));
ajv.addSchema(primitiveSchema, primitiveSchema.$id);
ajv.addSchema(footprintSchema, footprintSchema.$id);
ajv.addSchema(errorTaxSchema, errorTaxSchema.$id);
const validate = ajv.compile(catalogSchema);

const catalog = JSON.parse(await readFile('packages/tf-l0-spec/spec/catalog.json', 'utf8'));
const issues = [];

// 1) Schema validation
if (!validate(catalog)) {
  for (const err of validate.errors || []) {
    addIssue(issues, 'error', 'schema', ajv.errorsText([err]));
  }
}

// 2) Deeper checks
if (!catalog?.primitives || !Array.isArray(catalog.primitives)) {
  addIssue(issues, 'error', 'structure', 'catalog.primitives missing/invalid');
} else {
  const seen = new Set();
  for (const p of catalog.primitives) {
    // IDs
    if (!p.id) addIssue(issues, 'error', 'id-missing', `missing id: ${p.name ?? '(unknown)'}`);
    else {
      if (seen.has(p.id)) addIssue(issues, 'error', 'id-duplicate', `duplicate id: ${p.id}`);
      seen.add(p.id);
      const m = /^tf:([a-z0-9\-]+)\/([a-z0-9\-]+)@(\d+)$/.exec(p.id);
      if (!m) addIssue(issues, 'error', 'id-format', `bad id ${p.id}`);
      else if (p.domain && p.domain !== m[1]) addIssue(issues, 'error', 'domain-mismatch', `id domain ${m[1]} != property domain ${p.domain} (${p.id})`);
    }

    const effects = Array.isArray(p.effects) ? p.effects : [];
    for (const e of effects) if (!EFFECT_FAMILIES.has(e)) addIssue(issues, 'warn', 'effect-unknown', `unknown effect '${e}' on ${p.id}`);

    // Storage footprints
    if (effects.includes('Storage.Read')) {
      if (!Array.isArray(p.reads) || p.reads.length === 0) addIssue(issues, 'error', 'reads-missing', `Storage.Read requires 'reads' on ${p.id}`);
      else for (const r of p.reads) if (!r.uri) addIssue(issues, 'error', 'reads-uri-missing', `reads entry missing uri on ${p.id}`);
    }
    if (effects.includes('Storage.Write')) {
      if (!Array.isArray(p.writes) || p.writes.length === 0) addIssue(issues, 'error', 'writes-missing', `Storage.Write requires 'writes' on ${p.id}`);
      else for (const r of p.writes) if (!r.uri) addIssue(issues, 'error', 'writes-uri-missing', `writes entry missing uri on ${p.id}`);
    }

    // Network QoS
    if (effects.includes('Network.In') || effects.includes('Network.Out')) {
      const qos = p.qos || {};
      if (!qos.delivery_guarantee) addIssue(issues, 'error', 'qos-delivery-missing', `Network.* requires qos.delivery_guarantee on ${p.id}`);
    }

    // Crypto hints
    if ((p.name || '').match(/encrypt|decrypt|sign|verify|secret/)) {
      if (!Array.isArray(p.data_classes) || p.data_classes.length === 0) addIssue(issues, 'warn', 'data-classes-missing', `Consider setting data_classes for crypto/secret op ${p.id}`);
    }

    // Pure should not declare footprints
    if (effects.includes('Pure')) {
      if ((Array.isArray(p.reads) && p.reads.length) || (Array.isArray(p.writes) && p.writes.length)) {
        addIssue(issues, 'warn', 'pure-footprints', `Pure primitive declares reads/writes on ${p.id}`);
      }
    }
  }
}

const summary = {
  errors: issues.filter(i => i.severity === 'error').length,
  warnings: issues.filter(i => i.severity === 'warn').length
};

await writeFile(path.join(OUT_DIR, 'report.json'), JSON.stringify({ issues, summary }, null, 2) + '\n', 'utf8');
await writeFile(path.join(OUT_DIR, 'summary.txt'), `errors=${summary.errors}\nwarnings=${summary.warnings}\n`, 'utf8');

if (summary.errors > 0) {
  console.error(`LINT FAILED: ${summary.errors} error(s), ${summary.warnings} warning(s). See out/0.4/lint/report.json`);
  process.exit(1);
} else {
  console.log(`Lint OK: ${summary.errors} error(s), ${summary.warnings} warning(s).`);
}
