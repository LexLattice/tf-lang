#!/usr/bin/env node
import { mkdirSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';

const __dir = dirname(fileURLToPath(import.meta.url));
const repoRoot = join(__dir, '..');
const out = join(repoRoot, 'out', '0.4', 'proofs');
const scriptsDir = join(repoRoot, 'scripts');
const flowsDir = join(repoRoot, 'examples', 'flows');
const files = [];
mkdirSync(out, { recursive: true });

function sh(cmd, args, opts = {}) {
  const result = spawnSync(cmd, args, { stdio: 'inherit', cwd: repoRoot, ...opts });
  if (result.status !== 0) process.exit(result.status ?? 1);
}

function emit(label, script, args) {
  const target = join(out, label);
  mkdirSync(dirname(target), { recursive: true });
  sh('node', [script, ...args, '-o', target]);
  files.push(label);
}

// 1) Alloy (structural)
emit(
  'storage_conflict.als',
  join(scriptsDir, 'emit-alloy.mjs'),
  [join(flowsDir, 'storage_conflict.tf')]
);
emit(
  'storage_ok.als',
  join(scriptsDir, 'emit-alloy.mjs'),
  [join(flowsDir, 'storage_ok.tf')]
);

// 2) SMT (structural constraints)
emit(
  'storage_conflict.smt2',
  join(scriptsDir, 'emit-smt.mjs'),
  [join(flowsDir, 'storage_conflict.tf')]
);
emit(
  'storage_ok.smt2',
  join(scriptsDir, 'emit-smt.mjs'),
  [join(flowsDir, 'storage_ok.tf')]
);

// 3) SMT Laws (axioms and 1 equivalence)
emit(
  'laws/idempotent_hash.smt2',
  join(scriptsDir, 'emit-smt-laws.mjs'),
  ['--law', 'idempotent:hash']
);
emit(
  'laws/write_idempotent_by_key.smt2',
  join(scriptsDir, 'emit-smt-laws.mjs'),
  ['--law', 'idempotent:write-by-key']
);
emit(
  'laws/inverse_roundtrip.smt2',
  join(scriptsDir, 'emit-smt-laws.mjs'),
  ['--law', 'inverse:serialize-deserialize']
);
emit(
  'laws/emit_commute.smt2',
  join(scriptsDir, 'emit-smt-laws.mjs'),
  ['--law', 'commute:emit-metric-with-pure']
);

// 4) SMT Properties (Par-safety + commute equivalence)
emit(
  'props/storage_conflict.smt2',
  join(scriptsDir, 'emit-smt-props.mjs'),
  ['par-safety', join(flowsDir, 'storage_conflict.tf')]
);
emit(
  'props/obs_pure_equiv.smt2',
  join(scriptsDir, 'emit-smt-props.mjs'),
  [
    'commute',
    join(flowsDir, 'obs_pure_EP.tf'),
    join(flowsDir, 'obs_pure_PE.tf')
  ]
);

// Index (deterministic)
writeFileSync(
  join(out, 'index.json'),
  JSON.stringify(
    {
      generated: '1970-01-01T00:00:00.000Z',
      files: [...files].sort((a, b) => a.localeCompare(b))
    }
  ) + '\n'
);
