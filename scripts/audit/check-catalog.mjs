import { readFile } from 'node:fs/promises';
import { CANONICAL_EFFECT_FAMILIES } from '../../packages/tf-l0-check/src/effect-lattice.mjs';

const KNOWN_EFFECTS = new Set(CANONICAL_EFFECT_FAMILIES);

async function readJson(path) {
    try {
        const content = await readFile(path, 'utf-8');
        return JSON.parse(content);
    } catch (e) {
        if (e.code === 'ENOENT') {
            return null;
        }
        throw e;
    }
}

/**
 * @returns {Promise<{
 *   effects_unrecognized: string[],
 *   prims_missing_effects: string[],
 *   laws_ref_missing_prims: string[]
 * }>}
 */
export async function checkCatalog() {
    const catalog = await readJson('packages/tf-l0-spec/spec/catalog.json');
    const laws = await readJson('packages/tf-l0-spec/spec/laws.json');

    const effects_unrecognized = new Set();
    const prims_missing_effects = [];
    const laws_ref_missing_prims = [];

    const catalog_prims = new Set(catalog?.primitives.map(p => p.id) || []);

    if (catalog && catalog.primitives) {
        for (const prim of catalog.primitives) {
            if (!prim.effects || prim.effects.length === 0) {
                prims_missing_effects.push(prim.id);
            } else {
                for (const effect of prim.effects) {
                    if (!KNOWN_EFFECTS.has(effect)) {
                        effects_unrecognized.add(effect);
                    }
                }
            }
        }
    }

    if (laws && laws.laws) {
        for (const law of laws.laws) {
            if (law.hasOwnProperty('equivalent')) {
                for (const primId of (law.equivalent || [])) {
                    if (!catalog_prims.has(primId)) {
                        laws_ref_missing_prims.push(law.id);
                    }
                }
            }
             if (law.hasOwnProperty('related')) {
                for (const primId of (law.related || [])) {
                    if (!catalog_prims.has(primId)) {
                        laws_ref_missing_prims.push(law.id);
                    }
                }
            }
        }
    }

    return {
        effects_unrecognized: [...effects_unrecognized],
        prims_missing_effects,
        laws_ref_missing_prims,
    };
}
