#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { execSync } from 'node:child_process';

const sha256 = (buf) => crypto.createHash('sha256').update(buf).digest('hex');
const readJSON = (file) => JSON.parse(fs.readFileSync(file, 'utf8'));

function listFiles(glob) {
  const out = execSync(`git ls-files -- ':(glob)${glob}'`, { encoding: 'utf8' }).trim();
  return out ? out.split(/\r?\n/).filter(Boolean) : [];
}

function verifyArea(examplesRoot, area) {
  const baseDir = path.join(examplesRoot, area);
  if (!fs.existsSync(baseDir)) return true;

  const manifestPath = path.join(baseDir, 'manifest.json');
  if (!fs.existsSync(manifestPath)) {
    console.error(`Missing manifest: ${manifestPath}`);
    return false;
  }

  const manifest = readJSON(manifestPath);
  const pattern = `${examplesRoot}/${area}/*.${area === 'pipelines' ? 'l0' : 'l0m'}.json`;
  const files = listFiles(pattern);

  const expected = new Map();
  for (const file of files) {
    const rel = path.relative(baseDir, file).replace(/\\/g, '/');
    expected.set(rel, sha256(fs.readFileSync(file)));
  }

  let ok = true;

  for (const key of expected.keys()) {
    if (!(key in manifest)) {
      console.error(`Manifest missing entry: ${manifestPath} -> ${key}`);
      ok = false;
    }
  }
  for (const key of Object.keys(manifest)) {
    if (!expected.has(key)) {
      console.error(`Manifest has extra entry: ${manifestPath} -> ${key}`);
      ok = false;
    }
  }

  for (const [rel, hash] of expected.entries()) {
    const recorded = (manifest[rel] || '').toLowerCase();
    if (recorded !== hash) {
      console.error(`Hash mismatch for ${rel} in ${manifestPath}: manifest ${recorded}, actual ${hash}`);
      ok = false;
    }
    const shaFile = path.join(baseDir, `${rel}.sha256`);
    if (!fs.existsSync(shaFile)) {
      console.error(`Missing checksum file: ${shaFile}`);
      ok = false;
    } else {
      const shaContents = fs.readFileSync(shaFile, 'utf8').trim().toLowerCase();
      if (shaContents !== hash) {
        console.error(`Checksum mismatch for ${shaFile}: file ${shaContents}, actual ${hash}`);
        ok = false;
      }
    }
  }

  return ok;
}

const pipelineFiles = listFiles('examples/*/pipelines/*.l0.json');
const exampleRoots = Array.from(new Set(pipelineFiles.map((file) => {
  const parts = file.split('/');
  return parts.slice(0, 2).join('/');
}))).sort();

let failed = false;
for (const root of exampleRoots) {
  if (!verifyArea(root, 'pipelines')) failed = true;
  if (!verifyArea(root, 'monitors')) failed = true;
}

if (failed) process.exit(1);
if (exampleRoots.length === 0) {
  console.log('No canonical manifests to verify.');
} else {
  console.log('Verified manifests for:');
  exampleRoots.forEach((root) => console.log(` - ${root}`));
}
