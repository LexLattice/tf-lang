#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

import { EFFECT_PRECEDENCE } from '../../packages/tf-l0-check/src/effect-lattice.mjs';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const ROOT = path.resolve(__dirname, '../..');

const CATALOG_PATH = path.join(ROOT, 'packages/tf-l0-spec/spec/catalog.json');
const LAWS_PATH = path.join(ROOT, 'packages/tf-l0-spec/spec/laws.json');
const OUT_PATH = path.join(ROOT, 'docs/l0-catalog.md');

async function loadJson(filePath, fallback) {
  try {
    const raw = await readFile(filePath, 'utf8');
    return JSON.parse(raw);
  } catch (err) {
    if (fallback !== undefined) {
      return fallback;
    }
    throw err;
  }
}

function toArray(value) {
  return Array.isArray(value) ? value.slice() : [];
}

function formatList(values) {
  if (!values || values.length === 0) return '—';
  return values.map(v => `\`${v}\``).join(', ');
}

function formatIo(entries) {
  const items = toArray(entries)
    .map(entry => {
      if (!entry || typeof entry !== 'object') {
        return '';
      }
      const uri = typeof entry.uri === 'string' ? entry.uri : '';
      const note = typeof entry.notes === 'string' && entry.notes.trim().length > 0 ? entry.notes.trim() : '';
      const parts = [];
      if (uri) {
        parts.push(`\`${uri}\``);
      }
      if (note) {
        parts.push(`(${note})`);
      }
      return parts.join(' ');
    })
    .filter(Boolean)
    .sort((a, b) => a.localeCompare(b));
  if (items.length === 0) {
    return '—';
  }
  return items.join('<br>');
}

function mapLaws(lawsData) {
  const out = new Map();
  const laws = toArray(lawsData?.laws);
  for (const law of laws) {
    const applies = toArray(law?.applies_to);
    const id = typeof law?.id === 'string' ? law.id : null;
    if (!id) continue;
    for (const prim of applies) {
      if (typeof prim !== 'string') continue;
      const existing = out.get(prim) || [];
      existing.push(id);
      out.set(prim, existing);
    }
  }
  for (const [key, list] of out.entries()) {
    list.sort((a, b) => a.localeCompare(b));
  }
  return out;
}

function buildDoc(catalog, lawMap) {
  const primitives = toArray(catalog?.primitives)
    .filter(prim => prim && typeof prim === 'object')
    .sort((a, b) => {
      const idA = String(a.id || '').toLowerCase();
      const idB = String(b.id || '').toLowerCase();
      if (idA < idB) return -1;
      if (idA > idB) return 1;
      return 0;
    });

  const lines = [];
  lines.push('# L0 Catalog (generated)');
  lines.push(`Primitives: ${primitives.length}`);
  lines.push(`Effects: ${EFFECT_PRECEDENCE.join(', ')}`);
  lines.push('');

  for (const prim of primitives) {
    const primId = String(prim.id || '');
    lines.push(`### ${primId}`);
    lines.push('');
    lines.push('| Effects | Input | Output | Laws |');
    lines.push('| --- | --- | --- | --- |');

    const effects = toArray(prim.effects)
      .map(eff => String(eff || ''))
      .filter(Boolean)
      .sort((a, b) => a.localeCompare(b));
    const reads = formatIo(prim.reads);
    const writes = formatIo(prim.writes);
    const laws = lawMap.get(primId) || [];

    lines.push(`| ${formatList(effects)} | ${reads} | ${writes} | ${formatList(laws)} |`);
    lines.push('');
  }

  return ensureTrailingNewline(lines.join('\n'));
}

function ensureTrailingNewline(payload) {
  const normalized = payload.replace(/\s+$/, match => match.includes('\n') ? '\n' : '');
  return normalized.endsWith('\n') ? normalized : `${normalized}\n`;
}

async function main() {
  const [catalog, laws] = await Promise.all([
    loadJson(CATALOG_PATH, { primitives: [] }),
    loadJson(LAWS_PATH, { laws: [] })
  ]);

  const lawMap = mapLaws(laws);
  const content = buildDoc(catalog, lawMap);
  await mkdir(path.dirname(OUT_PATH), { recursive: true });
  await writeFile(OUT_PATH, content, 'utf8');
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  await main();
}

export { buildDoc };
