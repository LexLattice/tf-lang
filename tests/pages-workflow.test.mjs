import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';

const pages = readFileSync('.github/workflows/pages.yml', 'utf8');

test('pages workflow has preview artifact and gated deploy', () => {
  assert.ok(pages.includes('pull_request'), 'missing pull_request trigger');
  assert.ok(pages.includes("if: github.ref == 'refs/heads/main'"), 'deploy job not gated to main');
});

const readme = readFileSync('README.md', 'utf8');

test('README has deployment badge', () => {
  assert.match(readme, /\[!\[.*\]\(https:\/\/github.com\/.*\/actions\/workflows\/pages.yml\/badge.svg\)\]\(https:\/\/.*github.io\/[^)]+\)/);
});
