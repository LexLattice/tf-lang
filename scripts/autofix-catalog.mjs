#!/usr/bin/env node
/**
 * Catalog autofixer.
 * Modes:
 *  --mode suggest (default): write patches & an autofixed copy under out/0.4/lint/, do not modify spec
 *  --apply: apply fixes in-place to packages/tf-l0-spec/spec/catalog.json (back up before writing)
 * Flags:
 *  --config <path>: JSON with defaults (network/storage/crypto)
 *  --fail-on-suggestions: exit non-zero if suggestions were generated (suggest mode only)
 *
 * Outputs (always):
 *  - out/0.4/lint/autofix-report.json (list of patches with reasons)
 *  - out/0.4/lint/autofix.patch.json (RFC6902-like patch array; best-effort)
 *  - out/0.4/lint/catalog.autofixed.json (the modified catalog)
 */
import { readFile, writeFile, mkdir, copyFile } from 'node:fs/promises';
import path from 'node:path';

const MODE = (process.argv.includes('--apply')) ? 'apply' : (getArg('--mode') || 'suggest');
const CONFIG_PATH = getArg('--config');
const FAIL_ON_SUGG = process.argv.includes('--fail-on-suggestions');
const SPEC_PATH = 'packages/tf-l0-spec/spec/catalog.json';
const OUT_DIR = 'out/0.4/lint';

const defaults = Object.freeze({
  network: { delivery_guarantee: "at-least-once", ordering: null, visibility_timeout_ms: null },
  storage: { footprint_uri_placeholder: "res://TODO/<domain>/<name>" },
  crypto: { data_classes: ["secrets"] },
  effects: [
    { re: "hash", add: ["Pure","Crypto"] },
    { re: "encode|decode|serialize|deserialize|compress|decompress|chunk|assemble|transform", add: ["Pure"] },
    { re: "encrypt|decrypt|sign|verify|derive-key|manage-secret|generate-key", add: ["Crypto"] },
    { re: "publish|request|acknowledge", add: ["Network.Out"] },
    { re: "subscribe", add: ["Network.In"] },
    { re: "read|list", add: ["Storage.Read"] },
    { re: "write|delete|compare-and-swap", add: ["Storage.Write"] },
    { re: "emit-metric|trace-span|log-event", add: ["Observability"] },
    { re: "authorize|policy", add: ["Policy"] },
    { re: "now", add: ["Time.Read"] },
    { re: "sleep", add: ["Time.Wait"] },
    { re: "random", add: ["Randomness.Read"] }
  ]
});

function getArg(flag){ const i = process.argv.indexOf(flag); return i>0 ? process.argv[i+1] : null; }
function clone(x){ return JSON.parse(JSON.stringify(x)); }
function canonicalize(v){ return JSON.stringify(sortKeys(v)); }
function sortKeys(v){ if(v===null||typeof v!=='object') return v; if(Array.isArray(v)) return v.map(sortKeys); const o={}; for(const k of Object.keys(v).sort()) o[k]=sortKeys(v[k]); return o; }
function parseId(id){ const m=/^tf:([a-z0-9\-]+)\/([a-z0-9\-]+)@(\d+)$/.exec(id||''); return m?{domain:m[1], name:m[2]}:{domain:null,name:null}; }

const config = CONFIG_PATH ? Object.assign({}, defaults, JSON.parse(await readFile(CONFIG_PATH,'utf8'))) : defaults;
await mkdir(OUT_DIR, { recursive: true });

const original = JSON.parse(await readFile(SPEC_PATH,'utf8'));
const modified = clone(original);
const patches = [];

function addPatch(path, op, before, after, reason) {
  patches.push({ op, path, from: before, to: after, reason });
}

function ensureEffects(p, idx){
  const e = Array.isArray(p.effects)?new Set(p.effects):new Set();
  if (e.size===0) {
    for (const rule of config.effects) {
      if (new RegExp(rule.re).test(p.name||'')) for (const a of rule.add) e.add(a);
    }
  }
  const arr = Array.from(e);
  if (JSON.stringify(arr)!==JSON.stringify(p.effects||[])) {
    addPatch(`/primitives/${idx}/effects`, p.effects? 'replace':'add', p.effects||[], arr, 'Autofix effects by name heuristics');
    p.effects = arr;
  }
}

function ensureFootprints(p, idx){
  const id = parseId(p.id);
  const placeholder = config.storage.footprint_uri_placeholder.replace('<domain>', id.domain||'domain').replace('<name>', id.name||'name');
  if ((p.effects||[]).includes('Storage.Read')) {
    if (!Array.isArray(p.reads) || p.reads.length===0) {
      const val=[{ uri: placeholder, mode: 'read', notes: 'AUTO: replace with exact pattern' }];
      addPatch(`/primitives/${idx}/reads`, p.reads? 'replace':'add', p.reads||[], val, 'Add placeholder reads footprint for Storage.Read');
      p.reads = val;
    } else {
      let mutated = false;
      const before = clone(p.reads);
      for (const r of p.reads) if (!r.mode) { r.mode='read'; mutated = true; }
      if (mutated) addPatch(`/primitives/${idx}/reads`, 'replace', before, p.reads, 'Add mode=read to reads entries');
    }
  }
  if ((p.effects||[]).includes('Storage.Write')) {
    if (!Array.isArray(p.writes) || p.writes.length===0) {
      const val=[{ uri: placeholder, mode: 'write', notes: 'AUTO: replace with exact pattern' }];
      addPatch(`/primitives/${idx}/writes`, p.writes? 'replace':'add', p.writes||[], val, 'Add placeholder writes footprint for Storage.Write');
      p.writes = val;
    } else {
      let mutated = false;
      const before = clone(p.writes);
      for (const r of p.writes) if (!r.mode) { r.mode='write'; mutated = true; }
      if (mutated) addPatch(`/primitives/${idx}/writes`, 'replace', before, p.writes, 'Add mode=write to writes entries');
    }
  }
}

function ensureQoS(p, idx){
  if ((p.effects||[]).some(e=>e==='Network.In'||e==='Network.Out')) {
    const before = clone(p.qos||{});
    const q = Object.assign({}, p.qos||{});
    if (!q.delivery_guarantee) q.delivery_guarantee = config.network.delivery_guarantee;
    if (q.ordering==null) q.ordering = Array.isArray(p.keys)&&p.keys.length>0 ? 'per-key' : 'none';
    if ((p.effects||[]).includes('Network.In') && q.visibility_timeout_ms==null && config.network.visibility_timeout_ms!=null) {
      q.visibility_timeout_ms = config.network.visibility_timeout_ms;
    }
    const changed = canonicalize(q)!==canonicalize(p.qos||{});
    if (changed) {
      addPatch(`/primitives/${idx}/qos`, p.qos? 'replace':'add', before, q, 'Fill QoS defaults for Network.*');
      p.qos = q;
    }
  }
}

function ensureDataClasses(p, idx){
  if ((p.name||'').match(/encrypt|decrypt|sign|verify|secret/)) {
    if (!Array.isArray(p.data_classes) || p.data_classes.length===0) {
      addPatch(`/primitives/${idx}/data_classes`, p.data_classes? 'replace':'add', p.data_classes||[], config.crypto.data_classes, 'Set default data_classes for crypto/secret op');
      p.data_classes = clone(config.crypto.data_classes);
    }
  }
}

modified.primitives?.forEach((p, idx) => {
  ensureEffects(p, idx);
  ensureFootprints(p, idx);
  ensureQoS(p, idx);
  ensureDataClasses(p, idx);
});

const have = patches.length > 0;
await writeFile(path.join(OUT_DIR,'autofix-report.json'), JSON.stringify({ patches, count: patches.length, mode: MODE }, null, 2) + '\n', 'utf8');
await writeFile(path.join(OUT_DIR,'autofix.patch.json'), JSON.stringify(patches, null, 2) + '\n', 'utf8');
await writeFile(path.join(OUT_DIR,'catalog.autofixed.json'), canonicalize(modified) + '\n', 'utf8');

if (MODE==='apply' && have) {
  // backup and replace in place
  await copyFile(SPEC_PATH, SPEC_PATH + '.bak');
  await writeFile(SPEC_PATH, canonicalize(modified) + '\n', 'utf8');
  console.log(`Applied ${patches.length} change(s) to ${SPEC_PATH} (backup at catalog.json.bak).`);
} else if (MODE==='apply') {
  console.log('No changes to apply.');
}

if (MODE!=='apply') {
  if (have) {
    console.log(`Autofix suggested ${patches.length} change(s). See out/0.4/lint/autofix-report.json`);
    if (FAIL_ON_SUGG) process.exit(2);
  } else {
    console.log('No suggestions. Catalog looks good.');
  }
}
