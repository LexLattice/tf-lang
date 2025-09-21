import { mkdir, mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import { join, dirname } from 'node:path';
import { tmpdir } from 'node:os';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { parseArgs } from 'node:util';
import { spawn } from 'node:child_process';

const scriptDir = dirname(fileURLToPath(import.meta.url));
const crateManifest = join(scriptDir, '..', 'packages', 'tf-l0-codegen-rs', 'Cargo.toml');

export async function generate(ir, { outDir }) {
  await mkdir(outDir, { recursive: true });
  const tmp = await mkdtemp(join(tmpdir(), 'tf-rs-codegen-'));
  const irPath = join(tmp, 'ir.json');
  await writeFile(irPath, JSON.stringify(ir, null, 2), 'utf8');

  try {
    await runCargo(['run', '--quiet', '--manifest-path', crateManifest, '--', '--ir', irPath, '--out', outDir]);
  } finally {
    await rm(tmp, { recursive: true, force: true });
  }
}

async function runCargo(args) {
  await new Promise((resolve, reject) => {
    const child = spawn('cargo', args, { stdio: 'inherit' });
    child.on('error', reject);
    child.on('exit', (code) => {
      if (code === 0) resolve();
      else reject(new Error(`cargo ${args.join(' ')} exited with code ${code}`));
    });
  });
}

async function main(argv) {
  const parsed = parseArgs({
    args: argv,
    options: {
      out: { type: 'string', short: 'o' },
    },
    allowPositionals: true,
  });

  const [irPath] = parsed.positionals;
  const outDir = parsed.values.out;

  if (!irPath) {
    console.error('Usage: node scripts/generate-rs.mjs <ir.json> -o <out-dir>');
    process.exit(2);
  }
  if (!outDir) {
    console.error('Missing -o <out-dir>');
    process.exit(2);
  }

  const raw = await readFile(irPath, 'utf8');
  const ir = JSON.parse(raw);
  await generate(ir, { outDir });
}

if (import.meta.url === pathToFileURL(process.argv[1]).href) {
  main(process.argv.slice(2)).catch((err) => {
    if (err && err.message) console.error(err.message);
    else console.error(err);
    process.exit(1);
  });
}
