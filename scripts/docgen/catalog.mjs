#!/usr/bin/env node
import { access, mkdir, readFile, writeFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const EFFECT_ORDER = [
  'Pure',
  'Observability',
  'Network.Out',
  'Storage.Read',
  'Storage.Write',
  'Crypto',
  'Policy',
  'Infra',
  'Time',
  'UI'
];

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

function resolveRepoRoot(root) {
  if (root) return root;
  return path.resolve(__dirname, '..', '..');
}

async function readJsonMaybe(filePath) {
  try {
    await access(filePath);
  } catch {
    return null;
  }
  const raw = await readFile(filePath, 'utf8');
  return JSON.parse(raw);
}

function uniqueSorted(list = []) {
  const seen = new Set();
  const out = [];
  for (const item of Array.isArray(list) ? list : []) {
    if (typeof item !== 'string') continue;
    if (seen.has(item)) continue;
    seen.add(item);
    out.push(item);
  }
  out.sort((a, b) => a.localeCompare(b));
  return out;
}

function formatList(list) {
  if (!list || list.length === 0) {
    return 'None';
  }
  return list.map(item => `\`${item}\``).join(', ');
}

function normalizeFootprints(entries) {
  if (!Array.isArray(entries)) {
    return [];
  }
  return entries
    .map(entry => ({
      mode: typeof entry?.mode === 'string' ? entry.mode : null,
      uri: typeof entry?.uri === 'string' ? entry.uri : null,
      notes: typeof entry?.notes === 'string' ? entry.notes : null
    }))
    .map(entry => ({
      mode: entry.mode || 'unspecified',
      uri: entry.uri || '—',
      notes: entry.notes || null
    }))
    .sort((a, b) => {
      const byUri = a.uri.localeCompare(b.uri);
      if (byUri !== 0) return byUri;
      const byMode = a.mode.localeCompare(b.mode);
      if (byMode !== 0) return byMode;
      const aNotes = a.notes || '';
      const bNotes = b.notes || '';
      return aNotes.localeCompare(bNotes);
    });
}

function formatFootprints(entries) {
  const normalized = normalizeFootprints(entries);
  if (normalized.length === 0) {
    return 'None';
  }
  return normalized
    .map(entry => {
      const parts = [`mode=${entry.mode}`, `uri=${entry.uri}`];
      if (entry.notes) {
        parts.push(`notes=${entry.notes}`);
      }
      return parts.join(', ');
    })
    .join('<br />');
}

function collectLawMap(lawsJson) {
  const map = new Map();
  if (!lawsJson || !Array.isArray(lawsJson.laws)) {
    return map;
  }
  for (const law of lawsJson.laws) {
    const lawId = typeof law?.id === 'string' ? law.id : null;
    if (!lawId) continue;
    const applies = Array.isArray(law.applies_to) ? law.applies_to : [];
    for (const target of applies) {
      if (typeof target !== 'string') continue;
      if (!map.has(target)) {
        map.set(target, []);
      }
      map.get(target).push(lawId);
    }
  }
  for (const [, arr] of map) {
    arr.sort((a, b) => a.localeCompare(b));
  }
  return map;
}

export async function generateCatalogDoc(options = {}) {
  const repoRoot = resolveRepoRoot(options.root);
  const catalogPath = path.join(repoRoot, 'packages', 'tf-l0-spec', 'spec', 'catalog.json');
  const lawsPath = path.join(repoRoot, 'packages', 'tf-l0-spec', 'spec', 'laws.json');
  const outPath = path.join(repoRoot, 'docs', 'l0-catalog.md');

  const catalog = JSON.parse(await readFile(catalogPath, 'utf8'));
  const lawsJson = await readJsonMaybe(lawsPath);
  const lawMap = collectLawMap(lawsJson);

  const primitives = Array.isArray(catalog?.primitives) ? catalog.primitives.slice() : [];
  primitives.sort((a, b) => {
    const aId = typeof a?.id === 'string' ? a.id : '';
    const bId = typeof b?.id === 'string' ? b.id : '';
    return aId.localeCompare(bId);
  });

  const lines = [];
  lines.push('# L0 Catalog (generated)');
  lines.push(`Primitives: ${primitives.length}`);
  lines.push(`Effects: ${EFFECT_ORDER.join(', ')}`);
  lines.push('');

  if (primitives.length === 0) {
    lines.push('_No primitives defined in the current catalog._');
    lines.push('');
  }

  for (const prim of primitives) {
    const primId = typeof prim?.id === 'string' ? prim.id : '(unknown)';
    const effects = uniqueSorted(prim?.effects);
    const reads = Array.isArray(prim?.reads) ? prim.reads : [];
    const writes = Array.isArray(prim?.writes) ? prim.writes : [];
    const laws = lawMap.get(primId) || [];

    lines.push(`### ${primId}`);
    lines.push('');
    lines.push('| Field | Value |');
    lines.push('| --- | --- |');
    lines.push(`| Effects | ${formatList(effects)} |`);
    lines.push(`| Input | ${formatFootprints(reads)} |`);
    lines.push(`| Output | ${formatFootprints(writes)} |`);
    lines.push(`| Laws | ${formatList(laws)} |`);
    lines.push('');
  }

  const output = lines.join('\n').replace(/\s+$/u, '').concat('\n');
  await mkdir(path.dirname(outPath), { recursive: true });
  await writeFile(outPath, output, 'utf8');
  return outPath;
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  await generateCatalogDoc();
}
