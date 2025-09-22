// @tf-test kind=infra area=pages speed=fast deps=node

import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { join, dirname } from 'node:path';
import { describe, it, expect } from 'vitest';

const __dirname = dirname(fileURLToPath(import.meta.url));
const root = join(__dirname, '..', '..');

describe('pages workflow', () => {
  const workflow = readFileSync(join(root, '.github/workflows/pages.yml'), 'utf8');
  it('handles PRs with preview artifacts', () => {
    expect(workflow).toMatch(/pull_request:/);
    expect(workflow).toMatch(/actions\/upload-pages-artifact@v3/);
  });
  it('deploys only on main', () => {
    expect(workflow).toMatch(/if:\s*github\.ref\s*==\s*'refs\/heads\/main'/);
  });
});

describe('README badge', () => {
  const readme = readFileSync(join(root, 'README.md'), 'utf8');
  it('links to live site', () => {
    expect(readme).toMatch(/https:\/\/github\.com\/LexLattice\/tf-lang\/actions\/workflows\/pages\.yml\/badge\.svg\?branch=main/);
    expect(readme).toMatch(/https:\/\/LexLattice\.github\.io\/tf-lang\//);
  });
});
