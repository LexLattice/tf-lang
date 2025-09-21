#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
import process from 'node:process';
import { pathToFileURL } from 'node:url';

import {
  CANONICAL_EFFECT_FAMILIES,
  commuteSymmetric,
  effectRank,
  normalizeFamily,
  effectOf
} from '../../packages/tf-l0-check/src/effect-lattice.mjs';
import { listLawNames } from '../../packages/tf-l0-proofs/src/smt-laws.mjs';

const OUTPUT_JSON = 'out/0.4/proofs/coverage.json';
const OUTPUT_DOC = 'docs/l0-proof-coverage.md';

export async function analyzeCoverage() {
  const lattice = buildLatticeView();
  const lawSpec = await loadLawSpec();
  const availableLawNames = new Set(listLawNames());

  const allowedPairs = computeAllowedPairs(lattice);
  const usedPairs = computeUsedPairs(lattice);

  const lawPairs = computeLawPairs(lawSpec);
  const lawBackedPairs = new Set(lawPairs.map(pairKey));

  const missingForUsed = [...usedPairs]
    .filter((key) => !lawBackedPairs.has(key))
    .map((key) => parseKey(key));
  const missingForAllowed = [...allowedPairs]
    .filter((key) => !lawBackedPairs.has(key))
    .map((key) => parseKey(key));

  const idempotentCoverage = analyzeIdempotentCoverage(lawSpec, availableLawNames);
  const inverseCoverage = analyzeInverseCoverage(lawSpec, availableLawNames);

  const coverage = {
    allowed: [...allowedPairs].map((key) => parseKey(key)),
    used: [...usedPairs].map((key) => parseKey(key)),
    law_backed: lawPairs,
    missing_laws_for_used: missingForUsed,
    missing_laws_for_allowed: missingForAllowed,
    missing_idempotent_laws: idempotentCoverage.missing,
    missing_inverse_laws: inverseCoverage.missing
  };

  return {
    coverage,
    lattice,
    lawSpec,
    availableLawNames,
    idempotentCoverage,
    inverseCoverage
  };
}

function buildLatticeView() {
  const precedence = CANONICAL_EFFECT_FAMILIES.map((family) => normalizeFamily(family));
  const rank = new Map(precedence.map((family, index) => [family, effectRank(family)]));
  return { precedence, rank };
}

async function loadLawSpec() {
  const raw = await readFile('packages/tf-l0-spec/spec/laws.json', 'utf8');
  const parsed = JSON.parse(raw);
  const laws = Array.isArray(parsed?.laws) ? parsed.laws : [];
  return laws;
}

function computeAllowedPairs(lattice) {
  const keys = new Set();
  const families = lattice.precedence;
  for (let i = 0; i < families.length; i += 1) {
    for (let j = i; j < families.length; j += 1) {
      const a = families[i];
      const b = families[j];
      if (commuteSymmetric(a, b)) {
        keys.add(pairKey([a, b]));
      }
    }
  }
  return keys;
}

function computeUsedPairs(lattice) {
  const keys = new Set();
  const families = lattice.precedence;
  for (let i = 0; i < families.length; i += 1) {
    for (let j = i; j < families.length; j += 1) {
      const a = families[i];
      const b = families[j];
      if (!commuteSymmetric(a, b)) {
        continue;
      }
      if (familiesRequireSwap(a, b, lattice.rank)) {
        keys.add(pairKey([a, b]));
      }
    }
  }
  return keys;
}

function familiesRequireSwap(a, b, rank) {
  const rankA = rank.get(normalizeFamily(a));
  const rankB = rank.get(normalizeFamily(b));
  if (rankA !== rankB) {
    return true;
  }
  if (normalizeFamily(a) === normalizeFamily(b)) {
    // Equal families require alphabetical/argument ordering to stabilize sequences.
    return true;
  }
  return false;
}

function computeLawPairs(laws) {
  const pairs = [];
  for (const entry of laws) {
    const kind = typeof entry?.kind === 'string' ? entry.kind : '';
    if (!kind.startsWith('commute')) {
      continue;
    }
    const families = toFamilies(entry?.applies_to ?? []);
    if (families.length < 2) {
      continue;
    }
    const [a, b] = families;
    pairs.push([normalizeFamily(a), normalizeFamily(b)].sort(compareFamilies));
  }
  pairs.sort(comparePairArrays);
  return pairs;
}

function analyzeIdempotentCoverage(laws, availableLawNames) {
  const missing = [];
  for (const entry of laws) {
    if (entry?.kind !== 'idempotent') {
      continue;
    }
    for (const name of toPrimNames(entry?.applies_to ?? [])) {
      const expected = `idempotent:${name}`;
      if (!availableLawNames.has(expected)) {
        missing.push({ primitive: name, expected_law: expected, source: entry.id ?? null });
      }
    }
  }
  return { missing };
}

function analyzeInverseCoverage(laws, availableLawNames) {
  const missing = [];
  for (const entry of laws) {
    if (entry?.kind !== 'inverse' && entry?.kind !== 'eq') {
      continue;
    }
    for (const [left, right] of toPrimPairs(entry?.applies_to ?? [])) {
      if (!left || !right) {
        continue;
      }
      const expected = `inverse:${left}-${right}`;
      const alternate = `inverse:${right}-${left}`;
      if (!availableLawNames.has(expected) && !availableLawNames.has(alternate)) {
        missing.push({
          left,
          right,
          expected_law: expected,
          alternate_law: alternate,
          source: entry.id ?? null
        });
      }
    }
  }
  return { missing };
}

function toFamilies(list) {
  const out = [];
  if (!Array.isArray(list)) {
    return out;
  }
  for (const entry of list) {
    if (typeof entry !== 'string') {
      continue;
    }
    if (entry.toLowerCase() === 'pure') {
      out.push('Pure');
      continue;
    }
    out.push(effectOf(entry, {}));
  }
  return out;
}

function toPrimNames(list) {
  const out = [];
  if (!Array.isArray(list)) {
    return out;
  }
  for (const entry of list) {
    if (typeof entry !== 'string') {
      continue;
    }
    const name = primName(entry);
    if (name) {
      out.push(name);
    }
  }
  return out;
}

function toPrimPairs(list) {
  const out = [];
  if (!Array.isArray(list)) {
    return out;
  }
  if (list.every((entry) => typeof entry === 'string')) {
    if (list.length >= 2) {
      const left = primName(list[0]);
      const right = primName(list[1]);
      if (left && right) {
        out.push([left, right]);
      }
    }
    return out;
  }
  for (const entry of list) {
    if (!Array.isArray(entry) || entry.length < 2) {
      continue;
    }
    const left = typeof entry[0] === 'string' ? primName(entry[0]) : '';
    const right = typeof entry[1] === 'string' ? primName(entry[1]) : '';
    if (left && right) {
      out.push([left, right]);
    }
  }
  return out;
}

function primName(primId) {
  if (typeof primId !== 'string') {
    return '';
  }
  const parts = primId.split('/');
  const last = parts[parts.length - 1] ?? '';
  const [name] = last.split('@');
  return name?.toLowerCase() ?? '';
}

function pairKey(pair) {
  const [a, b] = pair.map((family) => normalizeFamily(family));
  const sorted = [a, b].sort(compareFamilies);
  return `${sorted[0]}↔${sorted[1]}`;
}

function parseKey(key) {
  const [a, b] = key.split('↔');
  return [a, b];
}

function compareFamilies(left, right) {
  if (left === right) {
    return 0;
  }
  const rankLeft = effectRank(left);
  const rankRight = effectRank(right);
  if (rankLeft !== rankRight) {
    return rankLeft - rankRight;
  }
  return left < right ? -1 : 1;
}

function comparePairArrays(left, right) {
  const cmpA = compareFamilies(left[0], right[0]);
  if (cmpA !== 0) {
    return cmpA;
  }
  return compareFamilies(left[1], right[1]);
}

function formatTableRow(pair, allowed, used, backed) {
  const [a, b] = pair;
  const label = `${a} ↔ ${b}`;
  return `| ${label.padEnd(19)} |   ${allowed ? '✔' : '✖'}     |         ${used ? '✔' : '✖'}         |     ${backed ? '✔' : '✖'}      |`;
}

function buildSummaryMarkdown(coverage) {
  const rows = [];
  rows.push('# L0 Proof Coverage');
  rows.push('');
  rows.push('This file is auto-generated by `scripts/proofs/coverage.mjs`.');
  rows.push('');
  rows.push('| Pair                | Allowed | Used in normalize | Law exists |');
  rows.push('|---------------------|---------|-------------------|------------|');

  const allowedKeys = new Set(coverage.allowed.map(pairKey));
  const usedKeys = new Set(coverage.used.map(pairKey));
  const lawKeys = new Set(coverage.law_backed.map(pairKey));
  const allKeys = [...new Set([...allowedKeys, ...usedKeys, ...lawKeys])];
  allKeys.sort();

  for (const key of allKeys) {
    const pair = parseKey(key);
    const row = formatTableRow(
      pair,
      allowedKeys.has(key),
      usedKeys.has(key),
      lawKeys.has(key)
    );
    rows.push(row);
  }

  rows.push('');
  rows.push('## TODO');
  rows.push('');
  if (coverage.missing_laws_for_used.length === 0 && coverage.missing_idempotent_laws.length === 0 && coverage.missing_inverse_laws.length === 0) {
    rows.push('- All normalizer rewrites have law coverage.');
  } else {
    if (coverage.missing_laws_for_used.length > 0) {
      rows.push('- [ ] Add commutation laws for:');
      for (const [a, b] of coverage.missing_laws_for_used) {
        rows.push(`  - ${a} ↔ ${b}`);
      }
    }
    if (coverage.missing_idempotent_laws.length > 0) {
      rows.push('- [ ] Provide idempotency proofs for:');
      for (const entry of coverage.missing_idempotent_laws) {
        rows.push(`  - ${entry.primitive} (expected ${entry.expected_law})`);
      }
    }
    if (coverage.missing_inverse_laws.length > 0) {
      rows.push('- [ ] Provide inverse/equality proofs for:');
      for (const entry of coverage.missing_inverse_laws) {
        rows.push(
          `  - ${entry.left} ↔ ${entry.right} (expected ${entry.expected_law} or ${entry.alternate_law})`
        );
      }
    }
  }

  rows.push('');
  return rows.join('\n');
}

async function writeFileEnsuringDir(filePath, contents) {
  const resolved = resolve(filePath);
  await mkdir(dirname(resolved), { recursive: true });
  await writeFile(resolved, ensureTrailingNewline(contents), 'utf8');
}

function ensureTrailingNewline(text) {
  return text.endsWith('\n') ? text : `${text}\n`;
}

async function main(argv) {
  const { coverage } = await analyzeCoverage();
  const jsonText = JSON.stringify(coverage, null, 2);
  await writeFileEnsuringDir(OUTPUT_JSON, `${jsonText}\n`);
  const markdown = buildSummaryMarkdown(coverage);
  await writeFileEnsuringDir(OUTPUT_DOC, markdown);
  process.stdout.write(`wrote ${OUTPUT_JSON}\n`);
  process.stdout.write(`wrote ${OUTPUT_DOC}\n`);
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  // Node executes ESM main modules with matching import.meta.url.
  main(process.argv).catch((error) => {
    process.stderr.write(`${error.message}\n`);
    process.exit(1);
  });
}

