#!/usr/bin/env node
import { readFile, mkdir, writeFile } from 'node:fs/promises';
import { basename, dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const HERE = dirname(fileURLToPath(import.meta.url));
const ROOT = resolve(HERE, '..');
const TEMPLATE_DIR = join(ROOT, 'packages', 'tf-l0-codegen-rs', 'templates');

export async function generateRustCrate(irPath, outDir) {
  if (!irPath) {
    throw new Error('IR path is required');
  }
  if (!outDir) {
    throw new Error('Output directory is required');
  }

  const raw = await readFile(irPath, 'utf8');
  const ir = JSON.parse(raw);
  const resolvedOutDir = resolve(outDir);
  const srcDir = join(resolvedOutDir, 'src');
  await mkdir(srcDir, { recursive: true });

  const crateName = deriveCrateName(ir, resolvedOutDir, irPath);
  const cargoTemplate = await loadTemplate('Cargo.toml');
  const libTemplate = await loadTemplate('lib.rs');
  const adaptersTemplate = await loadTemplate('adapters.rs');
  const pipelineTemplate = await loadTemplate('pipeline.rs');
  const runTemplate = await loadTemplate('run.rs');

  await writeFile(join(resolvedOutDir, 'Cargo.toml'), ensureNewline(cargoTemplate.replace(/\{\{package_name\}\}/g, crateName)), 'utf8');
  await writeFile(join(srcDir, 'lib.rs'), ensureNewline(libTemplate), 'utf8');
  await writeFile(join(srcDir, 'adapters.rs'), ensureNewline(adaptersTemplate), 'utf8');
  await writeFile(join(srcDir, 'pipeline.rs'), ensureNewline(pipelineTemplate), 'utf8');
  await writeFile(join(srcDir, 'run.rs'), ensureNewline(runTemplate.replace(/\{\{crate_name\}\}/g, crateName)), 'utf8');

  const irJson = `${JSON.stringify(ir, null, 2)}\n`;
  await writeFile(join(resolvedOutDir, 'ir.json'), irJson, 'utf8');

  return { crateName, outDir: resolvedOutDir };
}

async function loadTemplate(name) {
  return readFile(join(TEMPLATE_DIR, name), 'utf8');
}

function deriveCrateName(ir, outDir, irPath) {
  const baseName =
    (ir && typeof ir === 'object' && (ir.name || ir.pipeline?.name || ir.metadata?.name)) ||
    basename(outDir) ||
    basename(irPath).replace(/\.ir\.json$/i, '');
  return sanitizeCrateName(baseName);
}

function sanitizeCrateName(value) {
  const safe = String(value || '')
    .toLowerCase()
    .replace(/[^a-z0-9_]/g, '_')
    .replace(/_+/g, '_')
    .replace(/^_+/, '')
    .replace(/_+$/, '');
  return safe || 'tf_generated';
}

function ensureNewline(content) {
  return content.endsWith('\n') ? content : `${content}\n`;
}

function printUsage() {
  console.log('Usage: node scripts/generate-rs.mjs <ir.json> -o <output dir>');
}

async function main() {
  const args = process.argv.slice(2);
  if (args.length === 0 || args.includes('--help') || args.includes('-h')) {
    printUsage();
    return;
  }

  const irPath = args[0];
  let outDir = null;
  for (let i = 1; i < args.length; i += 1) {
    const arg = args[i];
    if (arg === '-o' || arg === '--out' || arg === '--out-dir') {
      i += 1;
      outDir = args[i];
    } else {
      throw new Error(`Unknown argument: ${arg}`);
    }
  }

  if (!outDir) {
    throw new Error('Output directory required via -o or --out');
  }

  const { crateName, outDir: resolvedOutDir } = await generateRustCrate(irPath, outDir);
  console.log(`wrote ${resolvedOutDir} (crate ${crateName})`);
}

const invokedDirectly =
  process.argv[1] && import.meta.url === pathToFileURL(resolve(process.argv[1])).href;

if (invokedDirectly) {
  main().catch((err) => {
    console.error(err && err.stack ? err.stack : err);
    process.exit(1);
  });
}
