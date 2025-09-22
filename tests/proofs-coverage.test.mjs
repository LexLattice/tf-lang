import { exec } from 'child_process';
import { promises as fs } from 'fs';
import path from 'path';
import assert from 'assert';

const SCRIPT_PATH = 'scripts/proofs/coverage.mjs';
const EMITTER_SCRIPT_PATH = 'scripts/proofs/emit-missing-laws.mjs';
const TEST_OUTPUT_DIR = 'out/0.4/proofs_test';
const COVERAGE_JSON_PATH = path.join(TEST_OUTPUT_DIR, 'coverage.json');
const COVERAGE_MD_PATH = path.join(TEST_OUTPUT_DIR, 'coverage.md');
const DOCS_PATH = 'docs/l0-proof-coverage-test.md';
const STUBS_DIR = path.join(TEST_OUTPUT_DIR, 'laws/stubs');

async function runScript(scriptPath, args = []) {
  return new Promise((resolve, reject) => {
    const command = `node ${scriptPath} ${args.join(' ')}`;
    exec(command, (error, stdout, stderr) => {
      if (error) {
        console.error(`Error executing: ${command}`);
        reject(error);
        return;
      }
      if (stderr) {
        console.error(`stderr for ${command}: ${stderr}`);
      }
      resolve(stdout);
    });
  });
}

async function testCoverageScript() {
  console.log('Running coverage script...');
  await runScript(SCRIPT_PATH, ['--out', TEST_OUTPUT_DIR]);
  const firstRunJson = await fs.readFile(COVERAGE_JSON_PATH, 'utf8');
  const firstRunMd = await fs.readFile(COVERAGE_MD_PATH, 'utf8');

  console.log('Running coverage script again for stability check...');
  await runScript(SCRIPT_PATH, ['--out', TEST_OUTPUT_DIR]);
  const secondRunJson = await fs.readFile(COVERAGE_JSON_PATH, 'utf8');
  const secondRunMd = await fs.readFile(COVERAGE_MD_PATH, 'utf8');

  assert.deepStrictEqual(JSON.parse(firstRunJson), JSON.parse(secondRunJson), 'Coverage JSON should be stable');
  console.log('Coverage JSON is stable.');
  assert.strictEqual(firstRunMd, secondRunMd, 'Coverage markdown should be stable');
  console.log('Coverage markdown is stable.');

  return JSON.parse(firstRunJson);
}

async function testDocsFlag() {
    console.log('Testing --docs flag...');
    await runScript(SCRIPT_PATH, ['--docs', DOCS_PATH]);
    const content = await fs.readFile(DOCS_PATH, 'utf8');
    assert(content.endsWith('\n'), `File ${DOCS_PATH} should end with a newline.`);
    console.log('--docs flag test passed.');
}

async function testEmitterScript(coverage) {
    if (!coverage.missing_laws_for_used || coverage.missing_laws_for_used.length === 0) {
        console.log('No missing laws to emit, skipping emitter test.');
        return;
    }

    console.log('Running emitter script...');
    await runScript(EMITTER_SCRIPT_PATH, ['--coverage-json', COVERAGE_JSON_PATH]);

    for (const pair of coverage.missing_laws_for_used) {
        const [familyA, familyB] = pair;
        const filename = `commute_${familyA}_${familyB}.smt2`.replace(/\./g, '_');
        const filepath = path.join(STUBS_DIR, filename);

        console.log(`Checking for stub file: ${filepath}`);
        const content = await fs.readFile(filepath, 'utf8');
        assert(content.endsWith('\n'), `File ${filename} should end with a newline.`);
        assert(content.includes(`commutation of ${familyA} and ${familyB}`), `File ${filename} should contain correct header.`);
    }
    console.log('Emitter script test passed.');
}

async function cleanup() {
    console.log('Cleaning up generated files...');
    try {
        await fs.rm(TEST_OUTPUT_DIR, { recursive: true, force: true });
        await fs.unlink(DOCS_PATH).catch(err => { if (err.code !== 'ENOENT') throw err; });
    } catch (err) {
        console.error('Error during cleanup:', err);
    }
}

async function main() {
  try {
    const coverage = await testCoverageScript();
    await testDocsFlag();
    await testEmitterScript(coverage);
    console.log('All tests passed!');
  } catch (error) {
    console.error('Test failed:', error);
    process.exit(1);
  } finally {
    await cleanup();
  }
}

main();
