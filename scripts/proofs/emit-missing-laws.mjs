import { promises as fs } from 'fs';
import path from 'path';

function parseArgs() {
    const args = process.argv.slice(2);
    const options = {
      coverageJson: 'out/0.4/proofs/coverage.json',
    };

    for (let i = 0; i < args.length; i++) {
      if (args[i] === '--coverage-json' && i + 1 < args.length) {
        options.coverageJson = args[i + 1];
        i++;
      }
    }
    return options;
  }

async function main() {
  const options = parseArgs();
  const coveragePath = path.resolve(process.cwd(), options.coverageJson);
  let coverageJson;
  try {
    coverageJson = await fs.readFile(coveragePath, 'utf8');
  } catch (err) {
      if (err.code === 'ENOENT') {
          console.error(`Coverage report not found at ${coveragePath}`);
          console.error('Run the coverage script first.');
          process.exit(1);
      }
      throw err;
  }

  const coverage = JSON.parse(coverageJson);

  const missingLaws = coverage.missing_laws_for_used;
  if (!missingLaws || missingLaws.length === 0) {
    console.log('No missing laws to emit.');
    return;
  }

  const stubsDir = path.resolve(path.dirname(coveragePath), 'laws/stubs');
  await fs.mkdir(stubsDir, { recursive: true });

  for (const pair of missingLaws) {
    const [familyA, familyB] = pair;
    const filename = `commute_${familyA}_${familyB}.smt2`.replace(/\./g, '_');
    const filepath = path.join(stubsDir, filename);

    const content = `
; Skeleton for commutation of ${familyA} and ${familyB}
(declare-sort Val 0)
(declare-fun ${familyA.replace('.','_')} (Val) Val)
(declare-fun ${familyB.replace('.','_')} (Val) Val)

(assert (forall ((x Val)) (= (${familyA.replace('.','_')} (${familyB.replace('.','_')} x)) (${familyB.replace('.','_')} (${familyA.replace('.','_')} x)))))

(declare-const input Val)
(define-fun seqAB () Val (${familyA.replace('.','_')} (${familyB.replace('.','_')} input)))
(define-fun seqBA () Val (${familyB.replace('.','_')} (${familyA.replace('.','_')} input)))

(assert (not (= seqAB seqBA)))
(check-sat)
`.trim() + '\n';

    await fs.writeFile(filepath, content);
    console.log(`Wrote stub file: ${filepath}`);
  }
}

main().catch(err => {
  console.error(err);
  process.exit(1);
});
