import { readdir, readFile, stat } from 'node:fs/promises';
import { join, resolve } from 'node:path';
import YAML from 'yaml';

const IGNORED_DIRS = new Set(['.git', 'node_modules', '.act', 'out']);

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
        yield res;
      }
    }
  } catch (error) {
    if (error.code !== 'ENOENT') {
      console.error(`Error reading directory ${dir}:`, error);
    }
  }
}

async function getScriptsFromWorkflows() {
    const scripts = new Set();
    const workflowsDir = '.github/workflows';
    try {
        const files = await readdir(workflowsDir);
        for (const file of files) {
            if (!file.endsWith('.yml') && !file.endsWith('.yaml')) continue;

            const workflowPath = join(workflowsDir, file);
            const content = await readFile(workflowPath, 'utf-8');
            const workflow = YAML.parse(content);

            if (workflow && workflow.jobs) {
                for (const job of Object.values(workflow.jobs)) {
                    if (job.steps) {
                        for (const step of job.steps) {
                            if (step.run) {
                                const lines = step.run.split('\n');
                                for (const line of lines) {
                                    const trimmedLine = line.trim();
                                    const match = trimmedLine.match(/^(?:node|bash|sh)\s+([^\s&]+)/);
                                    if (match && (match[1].endsWith('.mjs') || match[1].endsWith('.sh'))) {
                                        scripts.add(resolve(match[1]));
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    } catch (e) {
        // ignore if workflows dir does not exist
    }
    return scripts;
}


/**
 * @returns {Promise<Array<{path: string, issue: 'missing_newline'|'has_crlf'|'missing_exec'|'missing_shebang'}>>}
 */
export async function checkDeterminism() {
  const issues = [];
  const workflowScripts = await getScriptsFromWorkflows();

  for await (const file of getFiles()) {
    if (file.endsWith('.mjs') || file.endsWith('.json') || file.endsWith('.smt2') || file.endsWith('.als')) {
      const content = await readFile(file, 'utf-8');
      if (content.length > 0 && !content.endsWith('\n')) {
        issues.push({ path: file, issue: 'missing_newline' });
      }
    }

    if (file.endsWith('.json') || file.endsWith('.smt2') || file.endsWith('.als')) {
      const content = await readFile(file, 'utf-8');
      if (content.includes('\r\n')) {
        issues.push({ path: file, issue: 'has_crlf' });
      }
    }

    if (file.startsWith('packages/') && file.includes('/bin/') && file.endsWith('.mjs')) {
        try {
            const stats = await stat(file);
            if (!(stats.mode & 0o111)) {
                issues.push({ path: file, issue: 'missing_exec' });
            }
        } catch(e) {
            // ignore if file not found
        }
    }

    if (workflowScripts.has(resolve(file))) {
        const content = await readFile(file, 'utf-8');
        if (!content.startsWith('#!')) {
            issues.push({ path: file, issue: 'missing_shebang' });
        }
    }
  }

  return issues;
}
