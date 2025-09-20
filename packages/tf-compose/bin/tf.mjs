#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { basename, dirname } from 'node:path';

import { parseDSL } from '../src/parser.mjs';
import { canon } from '../src/canon.mjs';
import { hash, canonicalize } from '../../tf-l0-ir/src/hash.mjs';
import { checkIR } from '../../tf-l0-check/src/check.mjs';
import { manifestFromVerdict } from '../../tf-l0-check/src/manifest.mjs';
import { checkRegions } from '../../tf-l0-check/src/regions.mjs';

async function loadCatalog() {
  try {
    return JSON.parse(await readFile('packages/tf-l0-spec/spec/catalog.json', 'utf8'));
  } catch {
    return { primitives: [] };
  }
}

const rawArgs = process.argv.slice(2);
const args = rawArgs[0] === '--' ? rawArgs.slice(1) : rawArgs;
const cmd = args[0];
const validCommands = new Set(['parse', 'check', 'canon', 'emit', 'manifest', 'fmt', 'show']);

if (!cmd || !validCommands.has(cmd)) {
  console.error('Usage: tf <parse|check|canon|emit|manifest|fmt|show> <flow.tf> [--out path] [--lang ts|rs] [--write|-w]');
  process.exit(2);
}

if (cmd === 'fmt') {
  await handleFmt(args.slice(1));
  process.exit(0);
}

if (cmd === 'show') {
  await handleShow(args.slice(1));
  process.exit(0);
}

function arg(k) { const i = args.indexOf(k); return i >= 0 ? args[i + 1] : null; }

const optionKeys = new Set(['--out', '-o', '--lang']);
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

const src = await readFile(file, 'utf8');
const ir = parseDSL(src);
const cat = await loadCatalog();

if (cmd === 'parse') {
  const s = canonicalize(ir) + '\n';
  if (out) { await mkdir(dirname(out), { recursive: true }); await writeFile(out, s, 'utf8'); }
  else process.stdout.write(s);
  process.exit(0);
}

if (cmd === 'check') {
  const verdict = checkIR(ir, cat);

  let protectedList = [];
  try {
    const p = JSON.parse(await readFile('packages/tf-l0-spec/spec/protected.json', 'utf8'));
    protectedList = p.protected_keywords || [];
  } catch { }
  const regionVerdict = checkRegions(ir, cat, protectedList);

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
  const norm = canon(ir, laws);
  const payload = canonicalize(norm) + '\n';
  if (out) { await mkdir(dirname(out), { recursive: true }); await writeFile(out, payload, 'utf8'); }
  else process.stdout.write(payload);
  process.exit(0);
}

if (cmd === 'manifest') {
  const verdict = checkIR(ir, cat);
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
    await gen.generate(ir, { outDir });
  } else if (lang === 'rs') {
    const gen = await import('../../tf-l0-codegen-rs/scripts/generate.mjs');
    await gen.generate(ir, { outDir });
  } else {
    console.error('Unknown language:', lang);
    process.exit(2);
  }
  console.log('Emitted', lang, 'to', outDir);
  process.exit(0);
}

async function handleFmt(argv) {
  const writeFlag = argv.includes('--write') || argv.includes('-w');
  const file = findFileArg(argv, new Set(['--write', '-w']));
  if (!file) {
    console.error('Missing flow path.');
    process.exit(2);
  }
  const src = await readFile(file, 'utf8');
  const ir = parseDSL(src);
  const formatted = formatFlow(ir);
  if (writeFlag) {
    await writeFile(file, formatted, 'utf8');
  } else {
    process.stdout.write(formatted);
  }
}

async function handleShow(argv) {
  const file = findFileArg(argv, new Set());
  if (!file) {
    console.error('Missing flow path.');
    process.exit(2);
  }
  const src = await readFile(file, 'utf8');
  const ir = parseDSL(src);
  const tree = renderTree(ir);
  process.stdout.write(tree + '\n');
}

function findFileArg(argv, optionFlags) {
  for (let i = 0; i < argv.length; i++) {
    const token = argv[i];
    if (token === '--') continue;
    if (optionFlags.has(token)) continue;
    if (token.startsWith('-')) continue;
    return token;
  }
  return null;
}

function formatFlow(ir) {
  const lines = [];
  renderNode(ir, 0, false, lines);
  return lines.join('\n') + '\n';
}

function renderNode(node, indent, needsSemicolon, lines) {
  if (!node) return;
  const pad = ' '.repeat(indent);
  if (node.node === 'Prim') {
    let line = pad + formatPrim(node);
    if (needsSemicolon) line += ';';
    lines.push(line);
    return;
  }
  if (node.node === 'Seq') {
    renderBlock('seq', node.children || [], indent, needsSemicolon, lines);
    return;
  }
  if (node.node === 'Par') {
    renderBlock('par', node.children || [], indent, needsSemicolon, lines);
    return;
  }
  if (node.node === 'Region') {
    renderRegion(node, indent, needsSemicolon, lines);
    return;
  }
  throw new Error(`Unknown node: ${node.node}`);
}

function renderBlock(name, children, indent, needsSemicolon, lines) {
  const pad = ' '.repeat(indent);
  lines.push(`${pad}${name}{`);
  for (let i = 0; i < children.length; i++) {
    renderNode(children[i], indent + 2, i < children.length - 1, lines);
  }
  lines.push(`${pad}}${needsSemicolon ? ';' : ''}`);
}

function renderRegion(node, indent, needsSemicolon, lines) {
  const pad = ' '.repeat(indent);
  const name = node.kind === 'Transaction' ? 'txn' : 'authorize';
  const attrs = formatRegionAttrs(node.attrs || {});
  lines.push(`${pad}${name}${attrs}{`);
  const children = node.children || [];
  for (let i = 0; i < children.length; i++) {
    renderNode(children[i], indent + 2, i < children.length - 1, lines);
  }
  lines.push(`${pad}}${needsSemicolon ? ';' : ''}`);
}

function formatPrim(node) {
  const name = node.prim;
  const args = node.args || {};
  const keys = Object.keys(args).sort((a, b) => a.localeCompare(b));
  if (keys.length === 0) return name;
  const parts = keys.map((key) => `${key}=${formatLiteral(args[key])}`);
  return `${name}(${parts.join(', ')})`;
}

function formatRegionAttrs(attrs) {
  const keys = Object.keys(attrs).sort((a, b) => a.localeCompare(b));
  if (keys.length === 0) return '';
  const parts = keys.map((key) => `${key}=${formatLiteral(attrs[key])}`);
  return `(${parts.join(', ')})`;
}

function formatLiteral(value) {
  if (value === null) return 'null';
  if (Array.isArray(value)) {
    return `[${value.map((v) => formatLiteral(v)).join(', ')}]`;
  }
  if (typeof value === 'object') {
    const keys = Object.keys(value).sort((a, b) => a.localeCompare(b));
    const parts = keys.map((key) => `${key}:${formatLiteral(value[key])}`);
    return `{${parts.join(', ')}}`;
  }
  if (typeof value === 'string') {
    return JSON.stringify(value);
  }
  return String(value);
}

function renderTree(node) {
  const lines = [];
  emitTree(node, 0, lines);
  return lines.join('\n');
}

function emitTree(node, indent, lines) {
  if (!node) return;
  const pad = ' '.repeat(indent);
  if (node.node === 'Prim') {
    const args = node.args || {};
    const suffix = formatArgsInline(args);
    lines.push(`${pad}Prim: ${node.prim}${suffix}`);
    return;
  }
  if (node.node === 'Seq') {
    lines.push(`${pad}Seq`);
    for (const child of node.children || []) emitTree(child, indent + 2, lines);
    return;
  }
  if (node.node === 'Par') {
    lines.push(`${pad}Par`);
    for (const child of node.children || []) emitTree(child, indent + 2, lines);
    return;
  }
  if (node.node === 'Region') {
    const name = node.kind || 'Region';
    const attrs = formatArgsInline(node.attrs || {}, '(', ')');
    const label = name.charAt(0).toUpperCase() + name.slice(1);
    lines.push(`${pad}Region: ${label}${attrs}`);
    for (const child of node.children || []) emitTree(child, indent + 2, lines);
    return;
  }
  lines.push(`${pad}${node.node || 'Unknown'}`);
}

function formatArgsInline(args, open = ' {', close = '}') {
  const keys = Object.keys(args || {}).sort((a, b) => a.localeCompare(b));
  if (keys.length === 0) return '';
  const parts = keys.map((key) => `${key}:${formatLiteral(args[key])}`);
  return `${open}${parts.join(', ')}${close}`;
}
