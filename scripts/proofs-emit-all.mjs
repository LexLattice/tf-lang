#!/usr/bin/env node
import { mkdirSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';

const __dir = dirname(fileURLToPath(import.meta.url));
const root = join(__dir, '..');
const out = join(root, 'out', '0.4', 'proofs');
mkdirSync(out, { recursive: true });

function sh(cmd, args, opts = {}) {
  const result = spawnSync(cmd, args, { stdio: 'inherit', cwd: root, ...opts });
  if (result.status !== 0) {
    process.exit(result.status ?? 1);
  }
}

function emit(label, script, args) {
  const target = join(out, label);
  mkdirSync(dirname(target), { recursive: true });
  sh('node', [script, ...args, '-o', target]);
}

emit('storage_conflict.als', 'scripts/emit-alloy.mjs', ['examples/flows/storage_conflict.tf']);
emit('storage_ok.als', 'scripts/emit-alloy.mjs', ['examples/flows/storage_ok.tf']);

emit('storage_conflict.smt2', 'scripts/emit-smt.mjs', ['examples/flows/storage_conflict.tf']);
emit('storage_ok.smt2', 'scripts/emit-smt.mjs', ['examples/flows/storage_ok.tf']);

emit('laws/idempotent_hash.smt2', 'scripts/emit-smt-laws.mjs', ['--law', 'idempotent:hash']);
emit('laws/inverse_roundtrip.smt2', 'scripts/emit-smt-laws.mjs', ['--law', 'inverse:serialize-deserialize']);
emit('laws/emit_commute.smt2', 'scripts/emit-smt-laws.mjs', ['--law', 'commute:emit-metric-with-pure']);

emit('props/storage_conflict.smt2', 'scripts/emit-smt-props.mjs', ['par-safety', 'examples/flows/storage_conflict.tf']);
emit('props/obs_pure_equiv.smt2', 'scripts/emit-smt-props.mjs', ['commute', 'examples/flows/obs_pure_EP.tf', 'examples/flows/obs_pure_PE.tf']);

writeFileSync(
  join(out, 'index.json'),
  JSON.stringify(
    {
      generated: new Date(0).toISOString(),
      files: [
        'storage_conflict.als',
        'storage_ok.als',
        'storage_conflict.smt2',
        'storage_ok.smt2',
        'laws/idempotent_hash.smt2',
        'laws/inverse_roundtrip.smt2',
        'laws/emit_commute.smt2',
        'props/storage_conflict.smt2',
        'props/obs_pure_equiv.smt2'
      ]
    }
  ) + '\n'
);
