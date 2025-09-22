// @tf-test kind=proofs area=smt speed=medium deps=node
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, readFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { promisify } from 'node:util';
import { execFile } from 'node:child_process';

const execFileAsync = promisify(execFile);
const repoRoot = fileURLToPath(new URL('../', import.meta.url));
const suiteScript = fileURLToPath(new URL('../scripts/emit-smt-laws-suite.mjs', import.meta.url));

async function runSuite(outDir) {
  await execFileAsync(process.execPath, [suiteScript, '-o', outDir], {
    cwd: repoRoot
  });
}

test('law suite emits idempotent write obligation and inverse symmetry', async () => {
  const dirA = await mkdtemp(join(tmpdir(), 'smt-laws-a-'));
  await runSuite(dirA);

  const writeLaw = await readFile(join(dirA, 'write_idempotent_by_key.smt2'), 'utf8');
  assert.ok(
    writeLaw.includes('(define-fun once () Val (W u k ik v))'),
    'write idempotency defines a zero-arity once'
  );
  assert.ok(
    writeLaw.includes('(define-fun twice () Val (W u k ik (W u k ik v)))'),
    'write idempotency nests the second write'
  );
  assert.match(
    writeLaw,
    /\(assert \(not \(= twice once\)\)\)/,
    'write idempotency asserts disequality between twice and once'
  );
  assert.ok(writeLaw.trim().endsWith('(check-sat)'), 'write idempotency should end with check-sat');

  const inverseLaw = await readFile(join(dirA, 'inverse_roundtrip.smt2'), 'utf8');
  assert.ok(
    inverseLaw.includes('(forall ((v Val)) (= (D (S v)) v))'),
    'inverse law includes deserialize(serialize) axiom'
  );
  assert.ok(
    inverseLaw.includes('(forall ((b Bytes)) (= (S (D b)) b))'),
    'inverse law includes serialize(deserialize) axiom'
  );
  assert.ok(inverseLaw.trim().endsWith('(check-sat)'), 'inverse law should end with check-sat');

  const equivFile = await readFile(join(dirA, 'serialize_deserialize_equiv.smt2'), 'utf8');
  assert.match(equivFile, /\(define-fun outA/);
  assert.match(equivFile, /\(assert \(not \(= outA outB\)\)\)/);

  const dirB = await mkdtemp(join(tmpdir(), 'smt-laws-b-'));
  await runSuite(dirB);

  const files = ['idempotent_hash.smt2', 'inverse_roundtrip.smt2', 'emit_commute.smt2', 'write_idempotent_by_key.smt2', 'serialize_deserialize_equiv.smt2'];
  for (const file of files) {
    const first = await readFile(join(dirA, file), 'utf8');
    const second = await readFile(join(dirB, file), 'utf8');
    assert.equal(first, second, `${file} should be deterministic`);
  }
});
