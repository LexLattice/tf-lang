/**
 * A1: unify YAML catalogs into a normalized catalog.json.
 * For hard-grounding, we load ids.json and project each primitive into the catalog
 * with placeholders for effects/footprints/data_classes/errors to be filled in later.
 */
import { readFile, writeFile } from 'node:fs/promises';
import { join } from 'node:path';
import { canonicalize } from './canonical-json.mjs';

const spec = 'packages/tf-l0-spec/spec';

const ids = JSON.parse(await readFile(join(spec, 'ids.json'), 'utf8'));
const catalog = {
  catalog_semver: ids.catalog_semver || "0.4.0-alpha.0",
  primitives: ids.primitives.map(p => ({
    ...p,
    effects: [],
    reads: [],
    writes: [],
    keys: [],
    data_classes: [],
    errors: { retryable: false, categories: [] },
    qos: {}
  }))
};
await writeFile(join(spec, 'catalog.json'), canonicalize(catalog) + '\n', 'utf8');
console.log("catalog.json written with", catalog.primitives.length, "primitives.");
