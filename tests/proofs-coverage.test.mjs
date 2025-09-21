import { exec } from 'child_process';
import { promises as fs } from 'fs';
import path from 'path';
import assert from 'assert';

const SCRIPT_PATH = 'scripts/proofs/coverage.mjs';
const EMITTER_SCRIPT_PATH = 'scripts/proofs/emit-missing-laws.mjs';
const OUTPUT_PATH = 'out/0.4/proofs/coverage.json';
const MARKDOWN_OUTPUT_PATH = 'out/0.4/proofs/coverage.md';
const STUBS_DIR = 'out/0.4/proofs/laws/stubs';

async function runScript(scriptPath) {
  return new Promise((resolve, reject) => {
    exec(`node ${scriptPath}`, (error, stdout, stderr) => {
      if (error) {
        reject(error);
        return;
      }
      if (stderr) {
        console.error(`stderr: ${stderr}`);
      }
      resolve(stdout);
    });
  });
}

async function testCoverageScript() {
  console.log('Running coverage script...');
  await runScript(SCRIPT_PATH);
  const firstRunJson = await fs.readFile(OUTPUT_PATH, 'utf8');
  const firstRunMd = await fs.readFile(MARKDOWN_OUTPUT_PATH, 'utf8');

  console.log('Running coverage script again for stability check...');
  await runScript(SCRIPT_PATH);
  const secondRunJson = await fs.readFile(OUTPUT_PATH, 'utf8');
  const secondRunMd = await fs.readFile(MARKDOWN_OUTPUT_PATH, 'utf8');

  assert.deepStrictEqual(JSON.parse(firstRunJson), JSON.parse(secondRunJson), 'Coverage JSON should be stable');
  console.log('Coverage JSON is stable.');
  assert.strictEqual(firstRunMd, secondRunMd, 'Coverage markdown should be stable');
  console.log('Coverage markdown is stable.');

  return JSON.parse(firstRunJson);
}

async function testEmitterScript(coverage) {
    if (!coverage.missing_laws_for_used || coverage.missing_laws_for_used.length === 0) {
        console.log('No missing laws to emit, skipping emitter test.');
        return;
    }

    console.log('Running emitter script...');
    await runScript(EMITTER_SCRIPT_PATH);

    for (const pair of coverage.missing_laws_for_used) {
        const [familyA, familyB] = pair;
        const filename = `commute_${familyA}_${familyB}.smt2`.replace(/\./g, '_');
        const filepath = path.join(process.cwd(), STUBS_DIR, filename);

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
        await fs.unlink(OUTPUT_PATH);
        await fs.unlink(MARKDOWN_OUTPUT_PATH);
    } catch (err) {
        if (err.code !== 'ENOENT') {
            console.error('Error cleaning up coverage files:', err);
        }
    }
    try {
        await fs.rm(STUBS_DIR, { recursive: true, force: true });
    } catch (err) {
        console.error('Error cleaning up stubs directory:', err);
    }
}

async function main() {
  try {
    const coverage = await testCoverageScript();
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
