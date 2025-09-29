import { readFile } from 'node:fs/promises';

export async function readJsonFile(path, defaultValue = {}) {
  try {
    const raw = await readFile(path, 'utf8');
    return JSON.parse(raw);
  } catch (error) {
    if (error && error.code === 'ENOENT') {
      return defaultValue;
    }
    throw error;
  }
}
