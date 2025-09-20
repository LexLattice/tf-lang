import { readFile, writeFile } from 'node:fs/promises';
import { join } from 'node:path';
import { canonicalize } from './canonical-json.mjs';
const rules = JSON.parse(await readFile('packages/tf-l0-spec/rules/law-rules.json','utf8'));
await writeFile(join('packages/tf-l0-spec/spec','laws.json'), canonicalize(rules) + '\n', 'utf8');
console.log("laws.json written.");
