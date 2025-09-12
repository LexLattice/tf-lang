import { describe, it } from 'vitest';
import { execSync } from 'node:child_process';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

describe('esm build', () => {
  it('loads under node', () => {
    const pkgRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
    execSync('pnpm build', { cwd: pkgRoot, stdio: 'pipe' });
    execSync("node -e \"import('./dist/src/proof/index.js')\"", { cwd: pkgRoot, stdio: 'pipe' });
  });
});
