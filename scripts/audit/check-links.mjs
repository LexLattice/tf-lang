import { readdir, readFile, stat } from 'node:fs/promises';
import { dirname, join, resolve } from 'node:path';

const IGNORED_DIRS = new Set(['.git', 'node_modules', '.act', 'out']);
const GENERATED_DOCS = [
    'docs/l0-catalog.md',
    'docs/l0-dsl.md',
    'docs/l0-effects.md',
    'docs/pilot-l0.md',
    'docs/l0-proofs.md',
    'docs/l0-rust.md',
];

async function* getFiles(dir = '.') {
  try {
    const dirents = await readdir(dir, { withFileTypes: true });
    for (const dirent of dirents) {
      const res = join(dir, dirent.name);
      if (IGNORED_DIRS.has(dirent.name)) {
        continue;
      }
      if (dirent.isDirectory()) {
        yield* getFiles(res);
      } else {
        if (res.endsWith('.md')) {
            yield res;
        }
      }
    }
  } catch (error) {
    if (error.code !== 'ENOENT') {
      console.error(`Error reading directory ${dir}:`, error);
    }
  }
}

async function fileExists(path) {
    try {
        await stat(path);
        return true;
    } catch (e) {
        return false;
    }
}

/**
 * @returns {Promise<{broken: Array<{from: string, href: string}>}>}
 */
export async function checkLinks() {
    const broken = [];
    const filesToCheck = ['README.md'];

    for await (const file of getFiles('docs')) {
        filesToCheck.push(file);
    }

    for (const file of GENERATED_DOCS) {
        if (!await fileExists(file)) {
            // This is a special case, not a broken link from a file
            broken.push({ from: '.task-spec', href: file });
        }
    }

    const linkRegex = /\[[^\]]+\]\(([^)]+)\)/g;

    for (const from of filesToCheck) {
        const content = await readFile(from, 'utf-8');
        let match;
        while ((match = linkRegex.exec(content)) !== null) {
            const href = match[1];
            if (href.startsWith('http') || href.startsWith('#')) {
                continue;
            }

            const absolutePath = resolve(dirname(from), href);
            if (!await fileExists(absolutePath)) {
                broken.push({ from, href });
            }
        }
    }

    return { broken };
}
