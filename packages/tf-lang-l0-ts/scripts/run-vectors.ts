import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { VM } from '../src/vm/interpreter.js';
import { DummyHost } from '../src/host/memory.js';
import type { Host } from '../src/vm/opcode.js';
import { canonicalJsonBytes, blake3hex } from '../src/canon/index.js';

const toHex = (bytes: Uint8Array) => Buffer.from(bytes).toString('hex');

const unesc = (s: string) => s.replace(/~1/g, '/').replace(/~0/g, '~');
function ptrGet(obj: any, ptr: string): any {
  if (ptr === '/') return structuredClone(obj);
  const parts = ptr.split('/').slice(1).map(unesc);
  let cur: any = obj;
  for (const p of parts) {
    if (cur == null || typeof cur !== 'object') return null;
    if (Array.isArray(cur)) {
      const idx = Number(p);
      if (!Number.isInteger(idx) || idx < 0 || idx >= cur.length) return null;
      cur = cur[idx];
    } else {
      if (!(p in cur)) return null;
      cur = cur[p];
    }
  }
  return structuredClone(cur);
}
function ptrSet(obj: any, ptr: string, val: any): any {
  if (ptr === '/') return structuredClone(val);
  const parts = ptr.split('/').slice(1).map(unesc);
  const res = structuredClone(obj);
  let cur: any = res;
  for (let i = 0; i < parts.length - 1; i++) {
    const p = parts[i];
    if (Array.isArray(cur)) {
      const idx = Number(p);
      if (!Number.isInteger(idx) || idx < 0) return null;
      if (cur[idx] == null) cur[idx] = {};
      else if (typeof cur[idx] !== 'object') return null;
      cur = cur[idx];
    } else if (cur && typeof cur === 'object') {
      if (cur[p] == null) cur[p] = {};
      else if (typeof cur[p] !== 'object') return null;
      cur = cur[p];
    } else {
      return null;
    }
  }
  const last = parts[parts.length - 1];
  if (Array.isArray(cur)) {
    const idx = Number(last);
    if (!Number.isInteger(idx) || idx < 0) return null;
    if (idx >= cur.length) {
      for (let i = cur.length; i < idx; i++) cur[i] = {};
    }
    cur[idx] = structuredClone(val);
  } else if (cur && typeof cur === 'object') {
    cur[last] = structuredClone(val);
  } else {
    return null;
  }
  return res;
}

class EffectHost implements Host {
  constructor(private inner: Host) {}
  reads = new Set<string>();
  writes = new Set<string>();
  externals = new Set<string>();
  journal: any[] = [];

  private addRead(r: string) { this.reads.add(r); }
  private addWrite(r: string) { this.writes.add(r); }
  private addExternal(id: string) { this.externals.add(id); }

  async lens_project(state: any, region: string) {
    this.addRead(region);
    return ptrGet(state, region);
  }
  async lens_merge(state: any, region: string, sub: any) {
    this.addRead(region);
    this.addWrite(region);
    return ptrSet(state, region, sub);
  }
  async snapshot_make(state: any) {
    // record read of root
    this.addRead('/');
    return this.inner.snapshot_make(state);
  }
  async snapshot_id(snapshot: any) {
    return this.inner.snapshot_id(snapshot);
  }
  async diff_apply(state: any, delta: any) {
    return this.inner.diff_apply(state, delta);
  }
  async diff_invert(delta: any) {
    return this.inner.diff_invert(delta);
  }
  async journal_record(plan: any, delta: any, s0: string, s1: string, meta: any) {
    const entry = await this.inner.journal_record(plan, delta, s0, s1, meta);
    this.journal.push(delta);
    return entry;
  }
  async journal_rewind(world: any, entry: any) {
    return this.inner.journal_rewind(world, entry);
  }
  async call_tf(tf_id: string, args: any[]) {
    this.addExternal(tf_id);
    return this.inner.call_tf(tf_id, args);
  }
}

function normalizeEffect(h: EffectHost) {
  const norm = (set: Set<string>) => {
    if (set.has('/') && set.size > 1) set.delete('/');
    return Array.from(set).sort();
  };
  return {
    read: norm(h.reads),
    write: norm(h.writes),
    external: Array.from(h.externals).sort(),
  };
}

function lintVector(vec: any) {
  if (vec.bytecode.version !== 'L0') {
    throw new Error(`unsupported bytecode version: ${vec.bytecode.version}`);
  }
  const ptr = (p: string) => {
    if (typeof p === 'string' && !p.startsWith('/')) {
      throw new Error(`pointer must start with '/': ${p}`);
    }
  };
  for (const ins of vec.bytecode.instrs) {
    if ('region' in ins) ptr(ins.region);
    if ((ins.op === 'LENS_PROJ' || ins.op === 'LENS_MERGE') && ins.dst !== 0) {
      throw new Error('LENS ops must write to dst:0');
    }
  }
  const eff = vec.expected?.effect ?? {};
  for (const arr of [eff.read ?? [], eff.write ?? []]) {
    for (const p of arr) ptr(p);
  }
  for (const k of Object.keys(vec.inputs || {})) ptr(k);
  if (vec.expected?.delta != null) {
    const firstConst0 = vec.bytecode.instrs.find(
      (ins: any) => ins.op === 'CONST' && ins.dst === 0
    );
    if (!firstConst0) throw new Error('missing CONST dst:0 for initial state');
    const hasLens = vec.bytecode.instrs.some(
      (ins: any) => ins.op === 'LENS_PROJ' || ins.op === 'LENS_MERGE'
    );
    if (!hasLens) throw new Error('expected state change but no LENS_* op found');
  }
}

async function runVector(file: string) {
  const vec = JSON.parse(fs.readFileSync(file, 'utf8'));
  lintVector(vec);
  const host = new EffectHost(DummyHost);
  const vm = new VM(host);
  let delta: any = null;
  let err: any = null;
  try {
    delta = await vm.run(vec.bytecode);
  } catch (e) {
    err = e;
  }
  const effect = normalizeEffect(host);
  const journal = host.journal;
  const expected = vec.expected;
  let ok = false;
  if (expected.error) {
    ok = err?.message === expected.error &&
         Buffer.from(canonicalJsonBytes(expected.effect ?? {})).equals(Buffer.from(canonicalJsonBytes(effect))) &&
         Buffer.from(canonicalJsonBytes(expected.journal ?? [])).equals(Buffer.from(canonicalJsonBytes(journal)));
  } else if (!err) {
    ok = Buffer.from(canonicalJsonBytes({ delta, effect, journal })).equals(
      Buffer.from(canonicalJsonBytes({ delta: expected.delta, effect: expected.effect, journal: expected.journal ?? [] }))
    );
  }
  if (ok) {
    console.log(`\u2713 ${vec.name}`);
  } else {
    console.error(`\u2717 ${vec.name}`);
    if (expected.error) {
      console.error('expected error:', expected.error);
      console.error('actual error:', err?.message);
    } else {
      console.error(toHex(canonicalJsonBytes({ delta: expected.delta, effect: expected.effect, journal: expected.journal ?? [] })));
      console.error(toHex(canonicalJsonBytes({ delta, effect, journal })));
    }
  }
  return { ok, name: vec.name, delta, effect, journal };
}

async function main() {
  const __dirname = path.dirname(fileURLToPath(import.meta.url));
  const dir = path.join(__dirname, '../../..', 'tests', 'vectors');
  const files = fs.readdirSync(dir).filter(f => f.endsWith('.json')).sort();
  const report: any[] = [];
  let allOk = true;
  for (const f of files) {
    const res = await runVector(path.join(dir, f));
    report.push({
      name: res.name,
      delta: res.delta,
      effect: res.effect,
      journal: res.journal,
      delta_hash: blake3hex(canonicalJsonBytes(res.delta ?? null)),
      effect_hash: blake3hex(canonicalJsonBytes(res.effect)),
      journal_hash: blake3hex(canonicalJsonBytes(res.journal ?? [])),
    });
    if (!res.ok) allOk = false;
  }
  const outDir = path.join(dir, '.out');
  fs.mkdirSync(outDir, { recursive: true });
  fs.writeFileSync(path.join(outDir, 'ts-report.json'), JSON.stringify(report, null, 2));
  if (!allOk) process.exit(1);
}

main().catch(err => { console.error(err); process.exit(1); });
