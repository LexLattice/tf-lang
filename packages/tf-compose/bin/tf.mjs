#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { basename, dirname, resolve } from 'node:path';

import { parseDSL } from '../src/parser.mjs';
import { formatDSL, renderIRTree } from '../src/format.mjs';
import { canon } from '../src/canon.mjs';
import { hash, canonicalize } from '../../tf-l0-ir/src/hash.mjs';
import { checkIR } from '../../tf-l0-check/src/check.mjs';
import { manifestFromVerdict } from '../../tf-l0-check/src/manifest.mjs';
import { checkRegions } from '../../tf-l0-check/src/regions.mjs';
import { expandIncludes, readText } from '../src/io.mjs';

async function loadCatalog() {
  try {
    return JSON.parse(await readFile('packages/tf-l0-spec/spec/catalog.json', 'utf8'));
  } catch {
    return { primitives: [] };
  }
}

async function run() {
  const rawArgs = process.argv.slice(2);
  const args = rawArgs[0] === '--' ? rawArgs.slice(1) : rawArgs;

  function arg(k) { const i = args.indexOf(k); return i >= 0 ? args[i + 1] : null; }

  const cmd = args[0];
  if (!cmd || ['parse', 'check', 'canon', 'emit', 'manifest', 'fmt', 'show'].indexOf(cmd) < 0) {
    console.error('Usage: tf <parse|check|canon|emit|manifest|fmt|show> <flow.tf> [--out path] [--lang ts|rs] [--write|-w]');
    process.exit(2);
  }
  const optionKeys = new Set(['--out', '-o', '--lang', '--base']);
  let file = null;
  for (let i = 1; i < args.length; i++) {
    const token = args[i];
    if (optionKeys.has(token)) { i++; continue; }
    if (token === '--') continue;
    if (token.startsWith('-')) continue;
    file = token;
    break;
  }
  if (!file) {
    console.error('Missing flow path.');
    process.exit(2);
  }
  const out = arg('-o') || arg('--out');

  if (cmd === 'check' && file.endsWith('.l0.json')) {
    const { checkL0 } = await import('../../checker/check.mjs');
    const report = await checkL0(file);
    const target = out || 'out/TFREPORT.json';
    await mkdir(dirname(target), { recursive: true });
    await writeFile(target, `${JSON.stringify(report, null, 2)}\n`, 'utf8');
    console.log(`wrote ${target} (${report.status})`);
    process.exit(report.status === 'GREEN' ? 0 : 1);
  }

  const src = await readFile(file, 'utf8');
  const ir = parseDSL(src);

  if (cmd === 'fmt') {
    const write = args.includes('-w') || args.includes('--write');
    const formatted = formatDSL(ir);
    const payload = formatted.endsWith('\n') ? formatted : `${formatted}\n`;
    if (write) {
      await writeFile(file, payload, 'utf8');
    } else {
      process.stdout.write(payload);
    }
    process.exit(0);
  }

  if (cmd === 'show') {
    const tree = renderIRTree(ir);
    const payload = tree.length > 0 ? `${tree}\n` : '\n';
    process.stdout.write(payload);
    process.exit(0);
  }

  const baseDir = arg('--base') || dirname(file);
  let expanded;
  try {
    expanded = await expandIncludes(ir, {
      base: baseDir,
      loadFile: readText,
      parse: parseDSL,
      stack: [resolve(process.cwd(), file)]
    });
  } catch (err) {
    const message = err && typeof err.message === 'string' ? err.message : String(err);
    console.error(message);
    process.exit(1);
  }

  const cat = await loadCatalog();

  if (cmd === 'parse') {
    const s = canonicalize(expanded) + '\n';
    if (out) { await mkdir(dirname(out), { recursive: true }); await writeFile(out, s, 'utf8'); }
    else process.stdout.write(s);
    process.exit(0);
  }

  if (cmd === 'check') {
    const verdict = checkIR(expanded, cat);

    let protectedList = [];
    try {
      const p = JSON.parse(await readFile('packages/tf-l0-spec/spec/protected.json', 'utf8'));
      protectedList = p.protected_keywords || [];
    } catch { }
    const regionVerdict = checkRegions(expanded, cat, protectedList);

    const ok = Boolean(verdict.ok && regionVerdict.ok);
    const reasons = []
      .concat(verdict.reasons || [])
      .concat(regionVerdict.reasons || []);

    const payload = JSON.stringify({ ok, effects: verdict.effects || [], reasons }, null, 2) + '\n';
    if (out) { await mkdir(dirname(out), { recursive: true }); await writeFile(out, payload, 'utf8'); }
    else process.stdout.write(payload);
    process.exit(ok ? 0 : 1);
  }

  if (cmd === 'canon') {
    const laws = await readFile('packages/tf-l0-spec/spec/laws.json', 'utf8').then(JSON.parse).catch(() => ({ laws: [] }));
    const norm = canon(expanded, laws);
    const payload = canonicalize(norm) + '\n';
    if (out) { await mkdir(dirname(out), { recursive: true }); await writeFile(out, payload, 'utf8'); }
    else process.stdout.write(payload);
    process.exit(0);
  }

  if (cmd === 'manifest') {
    const verdict = checkIR(expanded, cat);
    const mani = manifestFromVerdict(verdict);
    const payload = JSON.stringify(mani, null, 2) + '\n';
    if (out) { await mkdir(dirname(out), { recursive: true }); await writeFile(out, payload, 'utf8'); }
    else process.stdout.write(payload);
    process.exit(0);
  }

  if (cmd === 'emit') {
    const lang = arg('--lang') || 'ts';
    const outDir = out || `out/0.4/codegen-${lang}/${basename(file, '.tf')}`;
    await mkdir(outDir, { recursive: true });
    if (lang === 'ts') {
      const gen = await import('../../tf-l0-codegen-ts/scripts/generate.mjs');
      await gen.generate(expanded, { outDir });
    } else if (lang === 'rs') {
      const gen = await import('../../tf-l0-codegen-rs/scripts/generate.mjs');
      await gen.generate(expanded, { outDir });
    } else {
      console.error('Unknown language:', lang);
      process.exit(2);
    }
    console.log('Emitted', lang, 'to', outDir);
    process.exit(0);
  }

  console.error('Usage: tf <parse|check|canon|emit|manifest|fmt|show> <flow.tf> [--out path] [--lang ts|rs] [--write|-w]');
  process.exit(2);
}

run().catch((err) => {
  if (err && typeof err.message === 'string') {
    console.error(err.message);
  } else {
    console.error(err);
  }
  process.exit(1);
});
