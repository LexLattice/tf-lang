#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { execSync } from 'node:child_process';

function sha256(buf) {
  return crypto.createHash('sha256').update(buf).digest('hex');
}

function readJSON(file) {
  return JSON.parse(fs.readFileSync(file, 'utf8'));
}

const pattern = process.argv[2] || 'examples/**/monitors/**/*.l0m.json';
const rawList = execSync(`git ls-files -- ':(glob)${pattern}'`, { encoding: 'utf8' }).trim();
const files = rawList ? rawList.split(/\r?\n/).filter(Boolean) : [];

let failed = false;

for (const monitorFile of files) {
  const bundle = readJSON(monitorFile);
  if (bundle.schemaVersion !== '0.6') {
    console.error(`Schema version must be 0.6 in ${monitorFile}`);
    failed = true;
  }
  const pipelineRef = bundle.pipelineRef;
  const badRef =
    typeof pipelineRef !== 'string' ||
    pipelineRef.startsWith('/') ||
    pipelineRef.includes('..') ||
    pipelineRef.includes('\\') ||
    !/^pipelines\/[a-z0-9][a-z0-9\-/\.]*\.l0\.json$/i.test(pipelineRef);

  if (badRef) {
    console.error(`Invalid pipelineRef in ${monitorFile}: ${pipelineRef}`);
    failed = true;
    continue;
  }

  const segments = monitorFile.split(path.sep);
  const examplesIdx = segments.indexOf('examples');
  if (examplesIdx === -1 || examplesIdx + 1 >= segments.length) {
    console.error(`Cannot resolve examples root for ${monitorFile}`);
    failed = true;
    continue;
  }

  const examplesRoot = segments.slice(0, examplesIdx + 2).join(path.sep);
  const pipelinePath = path.normalize(path.join(examplesRoot, pipelineRef));
  const pipelineDir = path.join(examplesRoot, 'pipelines');

  if (!pipelinePath.startsWith(pipelineDir + path.sep) && pipelinePath !== pipelineDir) {
    console.error(`pipelineRef must point inside pipelines/: ${monitorFile} -> ${pipelineRef}`);
    failed = true;
    continue;
  }

  if (!fs.existsSync(pipelinePath)) {
    console.error(`pipelineRef does not exist: ${monitorFile} -> ${pipelineRef}`);
    failed = true;
    continue;
  }

  const manifestPath = path.join(pipelineDir, 'manifest.json');
  if (!fs.existsSync(manifestPath)) {
    console.error(`Missing pipelines manifest near ${monitorFile}: ${manifestPath}`);
    failed = true;
    continue;
  }

  const manifest = readJSON(manifestPath);
  const relToPipelines = path.relative(pipelineDir, pipelinePath).replace(/\\/g, '/');
  const basename = path.basename(pipelinePath);
  const manifestKey = manifest.hasOwnProperty(relToPipelines)
    ? relToPipelines
    : manifest.hasOwnProperty(basename)
      ? basename
      : null;

  if (!manifestKey) {
    console.error(`Pipeline not present in manifest: ${monitorFile} -> ${pipelineRef}`);
    failed = true;
    continue;
  }

  const expectedHash = manifest[manifestKey];
  const actualHash = sha256(fs.readFileSync(pipelinePath));
  if (actualHash !== expectedHash) {
    console.error(`Pipeline hash mismatch for ${pipelineRef} (monitor ${monitorFile}): expected ${expectedHash}, got ${actualHash}`);
    failed = true;
  }
}

if (failed) process.exit(1);

if (!files.length) {
  console.log('No monitor bundles matched pattern, skipping reference check.');
} else {
  console.log(`Verified ${files.length} monitor bundle(s).`);
}
