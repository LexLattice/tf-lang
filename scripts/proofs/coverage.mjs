import {
  CANONICAL_EFFECT_FAMILIES,
  commuteSymmetric,
  effectOf,
} from '../../packages/tf-l0-check/src/effect-lattice.mjs';
import { promises as fs } from 'fs';
import path from 'path';

async function main() {
  const catalogPath = path.resolve(process.cwd(), 'packages/tf-l0-spec/spec/catalog.json');
  const catalogJson = await fs.readFile(catalogPath, 'utf8');
  const catalog = JSON.parse(catalogJson);

  const allowed_commutations = [];
  const seenPairs = new Set();

  for (let i = 0; i < CANONICAL_EFFECT_FAMILIES.length; i++) {
    for (let j = i; j < CANONICAL_EFFECT_FAMILIES.length; j++) {
      const familyA = CANONICAL_EFFECT_FAMILIES[i];
      const familyB = CANONICAL_EFFECT_FAMILIES[j];
      if (commuteSymmetric(familyA, familyB)) {
        const pair = [familyA, familyB].sort();
        const key = pair.join(',');
        if (!seenPairs.has(key)) {
            allowed_commutations.push(pair);
            seenPairs.add(key);
        }
      }
    }
  }

  // NOTE: The `normalize-commute.mjs` pass will reorder any adjacent pair
  // of primitives whose effects have a symmetric commutation property.
  // Therefore, the set of "used" commutations is the same as the set of
  // all symmetrically allowed commutations.
  const used_commutations = allowed_commutations;

  const lawsPath = path.resolve(process.cwd(), 'packages/tf-l0-spec/spec/laws.json');
  const lawsJson = await fs.readFile(lawsPath, 'utf8');
  const laws = JSON.parse(lawsJson).laws;

  const law_backed = [];
  const lawBackedPairs = new Set();

  for (const law of laws) {
    if (law.kind === 'commute-with-pure') {
      const primId = law.applies_to.find(id => id !== 'Pure');
      if (primId) {
        const family = effectOf(primId, catalog);
        const pair = ['Pure', family].sort();
        const pairKey = pair.join(',');
        if (!lawBackedPairs.has(pairKey)) {
          law_backed.push(pair);
          lawBackedPairs.add(pairKey);
        }
      }
    }
  }

  const smtLawsPath = path.resolve(process.cwd(), 'packages/tf-l0-proofs/src/smt-laws.mjs');
  const smtLawsContent = await fs.readFile(smtLawsPath, 'utf8');
  const commuteRegex = /'commute:([^']*)'/g;
  let match;
  while ((match = commuteRegex.exec(smtLawsContent)) !== null) {
    const lawName = match[1];
    const parts = lawName.split('-with-');
    if (parts.length === 2) {
        const familyA = normalizeFamilyName(parts[0].replace(/-/g, ' '));
        const familyB = normalizeFamilyName(parts[1].replace(/-/g, ' '));

        if (familyA && familyB) {
            const pair = [familyA, familyB].sort();
            const pairKey = pair.join(',');
            if (!lawBackedPairs.has(pairKey)) {
                law_backed.push(pair);
                lawBackedPairs.add(pairKey);
            }
        }
    }
  }

  const lawBackedSet = new Set(law_backed.map(p => p.join(',')));

  const missing_laws_for_used = used_commutations
    .filter(p => !lawBackedSet.has(p.join(',')))
    .map(p => p.sort());

  const missing_laws_for_allowed = allowed_commutations
    .filter(p => !lawBackedSet.has(p.join(',')))
    .map(p => p.sort());

  const idempotentRewrites = new Set();
  const inverseRewritesPairs = [];

  for (const law of laws) {
      if (law.kind === 'idempotent') {
          law.applies_to.forEach(prim => idempotentRewrites.add(getPrimName(prim)));
      } else if (law.kind === 'eq') {
          inverseRewritesPairs.push(law.applies_to.map(getPrimName).sort());
      }
  }

  const report = {
    allowed: allowed_commutations.map(p => p.sort()).sort(sortPairs),
    used: used_commutations.map(p => p.sort()).sort(sortPairs),
    law_backed: law_backed.map(p => p.sort()).sort(sortPairs),
    missing_laws_for_used: missing_laws_for_used.sort(sortPairs),
    missing_laws_for_allowed: missing_laws_for_allowed.sort(sortPairs),
    idempotency_laws: [...idempotentRewrites].sort(),
    inverse_laws: inverseRewritesPairs.map(p => p.join(' <-> ')).sort(),
  };

  const outputDir = path.resolve(process.cwd(), 'out/0.4/proofs');
  await fs.mkdir(outputDir, { recursive: true });

  const jsonOutputPath = path.join(outputDir, 'coverage.json');
  await fs.writeFile(jsonOutputPath, JSON.stringify(report, null, 2) + '\n');
  console.log(`Coverage report written to ${jsonOutputPath}`);

  await generateMarkdownReport(report, outputDir);
}

async function generateMarkdownReport(coverage, outputDir) {
    const {
        allowed,
        used,
        law_backed,
        missing_laws_for_used,
        idempotency_laws,
        inverse_laws,
      } = coverage;

      const allPairs = new Set([
          ...allowed.map(p => p.join(' <-> ')),
          ...used.map(p => p.join(' <-> ')),
          ...law_backed.map(p => p.join(' <-> ')),
      ]);

      const sortedPairs = [...allPairs].sort();

      const allowedSet = new Set(allowed.map(p => p.join(' <-> ')));
      const usedSet = new Set(used.map(p => p.join(' <-> ')));
      const lawBackedSet = new Set(law_backed.map(p => p.join(' <-> ')));

      let table = `| Pair | Allowed | Used in normalize | Law exists |\n`;
      table +=    `|---|---|---|---|\n`;

      for (const pair of sortedPairs) {
        const isAllowed = allowedSet.has(pair) ? '✔' : '✖';
        const isUsed = usedSet.has(pair) ? '✔' : '✖';
        const hasLaw = lawBackedSet.has(pair) ? '✔' : '✖';
        table += `| \`${pair}\` | ${isAllowed} | ${isUsed} | ${hasLaw} |\n`;
      }

      let todos = '## TODO\n\n';
      if (missing_laws_for_used.length > 0) {
        todos += '### Missing Commutation Laws\n\n';
        for (const pair of missing_laws_for_used) {
          todos += `- [ ] Add law for \`${pair.join(' <-> ')}\`\n`;
        }
      }

      const doc = `
# L0 Proof Coverage

This document provides a summary of the coverage of our proof system. It cross-checks the effect lattice and normalizer rules against our law and property emitters.

This file is auto-generated. Do not edit manually.

## Commutation Coverage

${table}

${todos}

## Idempotency and Inverse Laws

### Idempotency Laws

The following primitives have idempotency laws and are rewritten by the normalizer:

${idempotency_laws.map(p => `- \`${p}\``).join('\n')}

### Inverse Laws

The following pairs of primitives have inverse laws and are rewritten by the normalizer:

${inverse_laws.map(p => `- \`${p}\``).join('\n')}
`;

      const outputPath = path.join(outputDir, 'coverage.md');
      await fs.writeFile(outputPath, doc.trim() + '\n');
      console.log(`Markdown report written to ${outputPath}`);
}

function getPrimName(primId) {
    if (typeof primId !== 'string') return '';
    const parts = primId.split('/');
    const last = parts[parts.length - 1];
    if (!last) return '';
    const [name] = last.split('@');
    return name;
}

function normalizeFamilyName(name) {
    const family = name
        .split(' ')
        .map(word => word.charAt(0).toUpperCase() + word.slice(1))
        .join('');
    if (family === 'EmitMetric') return 'Observability';
    if (family === 'Pure') return 'Pure';
    return family;
}

function sortPairs(a, b) {
    const aKey = a.join(',');
    const bKey = b.join(',');
    if (aKey < bKey) return -1;
    if (aKey > bKey) return 1;
    return 0;
}

main().catch(err => {
  console.error(err);
  process.exit(1);
});
