#!/usr/bin/env node
import { readFile, writeFile } from 'node:fs/promises';
import { existsSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, '..', '..');
const DEFAULT_CATALOG_PATH = path.join(repoRoot, 'packages', 'tf-l0-spec', 'spec', 'catalog.json');
const DEFAULT_LAWS_PATH = path.join(repoRoot, 'packages', 'tf-l0-spec', 'spec', 'laws.json');
const DEFAULT_OUTPUT_PATH = path.join(repoRoot, 'docs', 'l0-catalog.md');

const EFFECT_LIST = [
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

function readOptionalJson(filePath) {
  if (!filePath || !existsSync(filePath)) {
    return null;
  }
  return readFile(filePath, 'utf8').then((data) => JSON.parse(data)).catch(() => null);
}

function escapeCell(value) {
  return String(value ?? '')
    .replace(/\r?\n/g, ' ')
    .replace(/\|/g, '\\|')
    .trim();
}

function formatFootprints(entries = []) {
  if (!Array.isArray(entries) || entries.length === 0) {
    return [];
  }
  const formatted = entries
    .map((entry) => {
      if (!entry || typeof entry !== 'object') {
        return '(unspecified)';
      }
      const uri = typeof entry.uri === 'string' && entry.uri.trim().length > 0 ? entry.uri.trim() : '(unspecified)';
      const details = [];
      if (entry.mode) {
        details.push(`mode=${entry.mode}`);
      }
      if (entry.notes) {
        details.push(`notes=${entry.notes}`);
      }
      if (details.length === 0) {
        return uri;
      }
      return `${uri} (${details.join(', ')})`;
    })
    .map((value) => escapeCell(value))
    .sort((a, b) => a.localeCompare(b));
  return formatted;
}

function gatherInputDetails(primitive) {
  const lines = [];
  const dataClasses = Array.isArray(primitive?.data_classes) ? primitive.data_classes.filter(Boolean) : [];
  if (dataClasses.length > 0) {
    const sorted = [...new Set(dataClasses.map(String))].sort((a, b) => a.localeCompare(b));
    lines.push(`Data classes: ${sorted.join(', ')}`);
  }
  const keys = Array.isArray(primitive?.keys) ? primitive.keys.filter(Boolean) : [];
  if (keys.length > 0) {
    const sorted = [...new Set(keys.map(String))].sort((a, b) => a.localeCompare(b));
    lines.push(`Keys: ${sorted.join(', ')}`);
  }
  const reads = formatFootprints(primitive?.reads);
  if (reads.length > 0) {
    lines.push(`Reads: ${reads.join('; ')}`);
  }
  return lines;
}

function gatherOutputDetails(primitive) {
  const lines = [];
  const writes = formatFootprints(primitive?.writes);
  if (writes.length > 0) {
    lines.push(`Writes: ${writes.join('; ')}`);
  }
  const qosEntries = primitive?.qos && typeof primitive.qos === 'object' ? Object.entries(primitive.qos) : [];
  if (qosEntries.length > 0) {
    const normalized = qosEntries
      .filter(([key, value]) => key && value != null && String(value).length > 0)
      .map(([key, value]) => `${key}=${value}`)
      .sort((a, b) => a.localeCompare(b));
    if (normalized.length > 0) {
      lines.push(`QoS: ${normalized.join(', ')}`);
    }
  }
  return lines;
}

function collectEffects(primitive) {
  const effects = Array.isArray(primitive?.effects) ? primitive.effects.filter(Boolean).map(String) : [];
  if (effects.length === 0) {
    return '—';
  }
  const sorted = [...new Set(effects)].sort((a, b) => a.localeCompare(b));
  return escapeCell(sorted.join(', '));
}

function collectLaws(primitive, laws = []) {
  if (!primitive?.id || !Array.isArray(laws)) {
    return '—';
  }
  const matches = laws
    .filter((law) => Array.isArray(law?.applies_to) && law.applies_to.map(String).includes(primitive.id))
    .map((law) => law.id)
    .filter(Boolean)
    .map(String)
    .sort((a, b) => a.localeCompare(b));
  if (matches.length === 0) {
    return '—';
  }
  return escapeCell(matches.join(', '));
}

function formatCell(lines) {
  if (!lines || lines.length === 0) {
    return '—';
  }
  return escapeCell(lines.join(' \u2022 '));
}

function buildCatalogMarkdown(catalog, lawsData) {
  const primitives = Array.isArray(catalog?.primitives) ? [...catalog.primitives] : [];
  primitives.sort((a, b) => {
    const ida = String(a?.id ?? '');
    const idb = String(b?.id ?? '');
    return ida.localeCompare(idb);
  });

  const laws = Array.isArray(lawsData?.laws) ? lawsData.laws : [];
  const lines = [];
  lines.push('# L0 Catalog (generated)');
  lines.push(`Primitives: ${primitives.length}`);
  lines.push(`Effects: ${EFFECT_LIST.join(', ')}`);

  for (const primitive of primitives) {
    lines.push('');
    lines.push(`### ${primitive.id}`);
    lines.push('');
    lines.push('| Effects | Input | Output | Laws |');
    lines.push('| --- | --- | --- | --- |');
    const effectsCell = collectEffects(primitive);
    const inputCell = formatCell(gatherInputDetails(primitive));
    const outputCell = formatCell(gatherOutputDetails(primitive));
    const lawsCell = collectLaws(primitive, laws);
    lines.push(`| ${effectsCell} | ${inputCell} | ${outputCell} | ${lawsCell} |`);
  }

  let doc = lines.join('\n');
  if (!doc.endsWith('\n')) {
    doc += '\n';
  }
  return doc;
}

export async function generateCatalogDoc({
  catalogPath = DEFAULT_CATALOG_PATH,
  lawsPath = DEFAULT_LAWS_PATH,
  outputPath = DEFAULT_OUTPUT_PATH
} = {}) {
  const catalog = JSON.parse(await readFile(catalogPath, 'utf8'));
  const laws = (await readOptionalJson(lawsPath)) ?? { laws: [] };
  const markdown = buildCatalogMarkdown(catalog, laws);
  await writeFile(outputPath, markdown, 'utf8');
  return markdown;
}

async function main() {
  await generateCatalogDoc();
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  await main();
}
