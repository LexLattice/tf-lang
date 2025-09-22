import { mkdir, writeFile } from 'node:fs/promises';
import { dirname } from 'node:path';

export async function writeJsonCanonical(file, obj) {
  await mkdir(dirname(file), { recursive: true });
  const json = JSON.stringify(obj, null, 2) + '\n';
  await writeFile(file, json, 'utf8');
}

export function sortTests(tests) {
  const by = (value) => (value ?? '').toString();
  return [...tests].sort((a, b) => {
    const fileCompare = by(a.file).localeCompare(by(b.file));
    if (fileCompare !== 0) return fileCompare;
    const kindCompare = by(a.kind).localeCompare(by(b.kind));
    if (kindCompare !== 0) return kindCompare;
    const areaCompare = by(a.area).localeCompare(by(b.area));
    if (areaCompare !== 0) return areaCompare;
    return by(a.speed).localeCompare(by(b.speed));
  });
}
