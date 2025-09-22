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

  const norm = value => value.toLowerCase().replace(/[^a-z0-9]+/g, '_');

  for (const [familyA, familyB] of [...missingLaws].sort((x, y) => x.join(',').localeCompare(y.join(',')))) {
    const filepath = path.join(stubsDir, `commute_${norm(familyA)}__${norm(familyB)}.smt2`);
    await fs.writeFile(
      filepath,
      [
        '(set-logic ALL)',
        `; TODO: law for commute ${familyA} <-> ${familyB}`,
        '',
      ].join('\n')
    );
    console.log(`Wrote stub file: ${filepath}`);
  }
}

main().catch(err => {
  console.error(err);
  process.exit(1);
});
