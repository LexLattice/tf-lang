#!/usr/bin/env node
import { readFile, writeFile } from 'node:fs/promises';
import { fileURLToPath, pathToFileURL } from 'node:url';
import path from 'node:path';

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

function repoRoot() {
  const here = fileURLToPath(new URL('.', import.meta.url));
  return path.resolve(here, '..', '..');
}

async function loadJsonMaybe(relPath) {
  try {
    const txt = await readFile(path.join(repoRoot(), relPath), 'utf8');
    return JSON.parse(txt);
  } catch {
    return null;
  }
}

function sortKeys(value) {
  if (Array.isArray(value)) {
    return value.map(sortKeys);
  }
  if (value && typeof value === 'object') {
    const entries = Object.entries(value)
      .map(([k, v]) => [k, sortKeys(v)])
      .sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0));
    return Object.fromEntries(entries);
  }
  return value;
}

function formatEffects(effects = []) {
  const items = Array.isArray(effects) ? [...effects] : [];
  items.sort((a, b) => a.localeCompare(b));
  return items.length > 0 ? items.join(', ') : '—';
}

function formatRecords(records = []) {
  if (!Array.isArray(records) || records.length === 0) {
    return '—';
  }
  const sorted = [...records].map(sortKeys).sort((a, b) => {
    const left = JSON.stringify(a);
    const right = JSON.stringify(b);
    return left.localeCompare(right);
  });
  return sorted
    .map(entry => {
      const pairs = Object.entries(entry)
        .map(([k, v]) => `${k}=${JSON.stringify(v)}`)
        .join(', ');
      return pairs.length > 0 ? `\`${pairs}\`` : '`{}`';
    })
    .join('<br>');
}

function collectLaws(lawsDoc, primId) {
  if (!lawsDoc || !Array.isArray(lawsDoc.laws)) {
    return [];
  }
  const id = (primId || '').toLowerCase();
  const found = new Set();
  for (const law of lawsDoc.laws) {
    const applies = Array.isArray(law?.applies_to) ? law.applies_to : [];
    for (const target of applies) {
      if (typeof target === 'string' && target.toLowerCase() === id) {
        if (typeof law.id === 'string' && law.id.length > 0) {
          found.add(law.id);
        }
      }
    }
  }
  return Array.from(found).sort((a, b) => a.localeCompare(b));
}

function formatLaws(lawIds) {
  if (!lawIds || lawIds.length === 0) {
    return '—';
  }
  return lawIds.map(id => `\`${id}\``).join('<br>');
}

function buildPrimitiveSection(primitive, lawsDoc) {
  const lines = [];
  const pid = primitive.id || 'unknown';
  lines.push(`### ${pid}`);
  const effects = formatEffects(primitive.effects);
  const inputs = formatRecords(primitive.reads);
  const outputs = formatRecords(primitive.writes);
  const lawIds = collectLaws(lawsDoc, pid);
  const laws = formatLaws(lawIds);
  lines.push('| Effects | Input | Output | Laws |');
  lines.push('| --- | --- | --- | --- |');
  lines.push(`| ${effects} | ${inputs} | ${outputs} | ${laws} |`);
  lines.push('');
  return lines;
}

async function main() {
  const catalog = (await loadJsonMaybe('packages/tf-l0-spec/spec/catalog.json')) || { primitives: [] };
  const laws = await loadJsonMaybe('packages/tf-l0-spec/spec/laws.json');
  const primitives = Array.isArray(catalog.primitives) ? [...catalog.primitives] : [];
  primitives.sort((a, b) => {
    const left = (a.id || '').toLowerCase();
    const right = (b.id || '').toLowerCase();
    return left.localeCompare(right);
  });

  const lines = [];
  lines.push('# L0 Catalog (generated)');
  lines.push(`Primitives: ${primitives.length}`);
  lines.push(`Effects: ${EFFECT_ORDER.join(', ')}`);
  lines.push('');

  for (const primitive of primitives) {
    lines.push(...buildPrimitiveSection(primitive, laws));
  }

  const outPath = path.join(repoRoot(), 'docs', 'l0-catalog.md');
  const payload = lines.join('\n');
  await writeFile(outPath, payload.endsWith('\n') ? payload : `${payload}\n`, 'utf8');
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  await main();
}
