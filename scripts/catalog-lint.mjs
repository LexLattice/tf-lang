#!/usr/bin/env node
/**
 * Catalog linter: enforces minimal invariants for effectful L0s and reference integrity for laws.
 * Exits non-zero on ERRORs; prints WARNings to stdout.
 * Produces: out/0.4/lint/report.json
 */
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { createHash } from 'node:crypto';

const LINT_LEVEL = (process.env.TF_LINT_LEVEL || 'error').toLowerCase(); // 'error' or 'warn'

function sha256(s){ return 'sha256:' + createHash('sha256').update(s).digest('hex'); }

function issue(level, prim, rule, msg){ return { level, prim_id: prim?.id || null, prim_name: prim?.name || null, rule, message: msg }; }

function isEffect(p, eff){ return (p.effects||[]).includes(eff); }

function hasFootprints(p, mode){
  const xs = (mode==='read') ? (p.reads||[]) : (p.writes||[]);
  return xs.length > 0;
}

function checkFootprints(p, mode){
  const xs = (mode==='read') ? (p.reads||[]) : (p.writes||[]);
  const errs = [];
  for (const f of xs) {
    if (typeof f.uri !== 'string' || !f.uri.startsWith('res://')) {
      errs.push(`footprint uri must start with 'res://', got ${String(f.uri)}`);
    }
    if (f.mode && f.mode !== mode) {
      errs.push(`footprint mode mismatch: expected '${mode}', got '${f.mode}'`);
    }
  }
  return errs;
}

function dedupeProblems(problems){
  const seen = new Set();
  const out = [];
  for (const p of problems) {
    const key = `${p.level}|${p.prim_id}|${p.rule}|${p.message}`;
    if (!seen.has(key)){ seen.add(key); out.push(p); }
  }
  return out;
}

async function main(){
  const catalog = JSON.parse(await readFile('packages/tf-l0-spec/spec/catalog.json','utf8'));
  let laws = { laws: [] };
  try { laws = JSON.parse(await readFile('packages/tf-l0-spec/spec/laws.json','utf8')); } catch {}

  const problems = [];
  const idSet = new Set();
  const nameKeySet = new Set();

  for (const p of catalog.primitives || []) {
    // ID & name basics
    if (!/^tf:[a-z0-9\-]+\/[a-z0-9\-]+@\d+$/.test(p.id || '')) {
      problems.push(issue('error', p, 'id-format', `invalid id format '${p.id}'`));
    }
    if (idSet.has(p.id)) {
      problems.push(issue('error', p, 'id-duplicate', `duplicate id '${p.id}'`));
    } else {
      idSet.add(p.id);
    }
    const nk = `${p.domain}|${p.name}`;
    if (nameKeySet.has(nk)) {
      problems.push(issue('error', p, 'name-duplicate', `duplicate (domain,name) '${nk}'`));
    } else {
      nameKeySet.add(nk);
    }

    // Effects / footprints invariants
    if (isEffect(p, 'Storage.Read') && !hasFootprints(p, 'read')) {
      problems.push(issue('error', p, 'storage-read-footprints', 'Storage.Read requires non-empty `reads[]` footprints'));
    } else {
      for (const e of checkFootprints(p, 'read')) problems.push(issue('error', p, 'reads-invalid', e));
    }

    if (isEffect(p, 'Storage.Write') && !hasFootprints(p, 'write')) {
      problems.push(issue('error', p, 'storage-write-footprints', 'Storage.Write requires non-empty `writes[]` footprints'));
    } else {
      for (const e of checkFootprints(p, 'write')) problems.push(issue('error', p, 'writes-invalid', e));
    }

    // Network QoS hints
    if ((p.effects||[]).some(e => e.startsWith('Network'))) {
      if (!p.qos || typeof p.qos !== 'object') {
        problems.push(issue('warn', p, 'network-qos-missing', 'Network primitive should declare `qos{delivery_guarantee,ordering}`'));
      } else if (!p.qos.delivery_guarantee) {
        problems.push(issue('warn', p, 'network-qos-delivery', 'qos.delivery_guarantee should be set (none|at-most-once|at-least-once|exactly-once)'));
      }
    }

    // Crypto hints
    if ((p.effects||[]).includes('Crypto') && Array.isArray(p.data_classes) && p.data_classes.length===0) {
      problems.push(issue('warn', p, 'crypto-data-classes', 'Crypto primitive should tag `data_classes` (e.g., secrets)'));
    }
  }

  // Law references check
  for (const law of laws.laws || []) {
    for (const id of law.applies_to || []) {
      if (!idSet.has(id)) problems.push({ level:'error', prim_id: id, prim_name: null, rule: 'law-ref-missing', message: `Law ${law.id} references unknown primitive '${id}'` });
    }
  }

  const report = {
    summary: {
      errors: problems.filter(p=>p.level==='error').length,
      warnings: problems.filter(p=>p.level==='warn').length
    },
    problems: dedupeProblems(problems)
  };

  await mkdir('out/0.4/lint', { recursive: true });
  await writeFile('out/0.4/lint/report.json', JSON.stringify(report, null, 2) + '\n', 'utf8');
  console.log(`Lint complete: ${report.summary.errors} error(s), ${report.summary.warnings} warning(s).`);
  if (report.summary.errors > 0 && LINT_LEVEL === 'error') process.exit(1);
}

main().catch(e => { console.error(e); process.exit(2); });
