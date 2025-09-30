import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { expandPipelineFromFile } from '../packages/expander/expand.mjs';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const repoRoot = path.resolve(__dirname, '..');

const inputPath = path.resolve(repoRoot, '0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml');
const outputPath = path.resolve(repoRoot, '0.6/build/auto.fnol.fasttrack.v1.l0.json');

const l0 = expandPipelineFromFile(inputPath);

fs.mkdirSync(path.dirname(outputPath), { recursive: true });
fs.writeFileSync(outputPath, JSON.stringify(l0, null, 2));
console.log(`expanded ${inputPath} -> ${outputPath}`);
