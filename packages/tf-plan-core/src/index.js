import { createHash } from 'node:crypto';
import { createRequire } from 'node:module';
import Ajv from 'ajv';
export const PLAN_GRAPH_VERSION = '0.1.0';
export function stableId(input) {
    const canonical = `${input.scope}:${input.specId}|${input.component}|${input.choice}|${input.seed}|${input.version}`;
    const full = createHash('sha256').update(canonical).digest('hex');
    return {
        full,
        short: full.slice(0, 12),
    };
}
export function deepFreeze(value) {
    if (value === null) {
        return value;
    }
    if (typeof value !== 'object') {
        return value;
    }
    const seen = new Set();
    const freeze = (target) => {
        if (target === null || typeof target !== 'object') {
            return target;
        }
        if (seen.has(target)) {
            return target;
        }
        seen.add(target);
        if (Array.isArray(target)) {
            for (const item of target) {
                freeze(item);
            }
        }
        else {
            const entries = Object.entries(target);
            for (const [, entryValue] of entries) {
                freeze(entryValue);
            }
        }
        return Object.freeze(target);
    };
    return freeze(value);
}
export function stableSort(items, compare) {
    return items
        .map((value, index) => ({ value, index }))
        .sort((left, right) => {
        const result = compare(left.value, right.value);
        if (result !== 0) {
            return result;
        }
        return left.index - right.index;
    })
        .map((entry) => entry.value);
}
function normalizeSeed(seed) {
    if (typeof seed === 'number' && Number.isFinite(seed)) {
        return seed >>> 0;
    }
    const text = typeof seed === 'string' ? seed : JSON.stringify(seed);
    const hash = createHash('sha256').update(text).digest();
    return hash.readUInt32BE(0);
}
export function seedRng(seed) {
    let state = normalizeSeed(seed) || 1;
    const next = () => {
        // Mulberry32 PRNG
        state |= 0;
        state = (state + 0x6D2B79F5) | 0;
        let t = Math.imul(state ^ (state >>> 15), 1 | state);
        t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
        return ((t ^ (t >>> 14)) >>> 0) / 0x100000000;
    };
    return {
        next,
        nextInt(maxExclusive) {
            if (!Number.isFinite(maxExclusive) || maxExclusive <= 0) {
                throw new Error(`maxExclusive must be a positive finite number, received ${maxExclusive}`);
            }
            return Math.floor(next() * maxExclusive);
        },
    };
}
export function canonicalStringify(value) {
    const serialize = (input) => {
        if (input === null || typeof input !== 'object') {
            return JSON.stringify(input);
        }
        if (Array.isArray(input)) {
            const items = input.map((element) => serialize(element));
            return `[${items.join(',')}]`;
        }
        const entries = Object.entries(input);
        entries.sort((left, right) => {
            if (left[0] < right[0]) {
                return -1;
            }
            if (left[0] > right[0]) {
                return 1;
            }
            return 0;
        });
        const parts = entries.map(([key, val]) => `${JSON.stringify(key)}:${serialize(val)}`);
        return `{${parts.join(',')}}`;
    };
    return serialize(value);
}
export function hashObject(value) {
    const canonical = canonicalStringify(value);
    return createHash('sha256').update(canonical).digest('hex');
}

const require = createRequire(import.meta.url);
function loadSchema(name) {
    const candidates = [`../../../schema/${name}`, `../../../../schema/${name}`];
    for (const candidate of candidates) {
        try {
            return require(candidate);
        }
        catch {
            continue;
        }
    }
    throw new Error(`Unable to load schema ${name}`);
}
function formatErrors(errors) {
    if (!errors || errors.length === 0) {
        return 'unknown error';
    }
    return errors
        .map((error) => {
        const instance = error.instancePath || '/';
        const message = error.message ?? 'validation error';
        return `${instance} ${message}`;
    })
        .join(', ');
}
function assertValid(value, validator, label) {
    if (validator(value)) {
        return value;
    }
    const details = formatErrors(validator.errors);
    throw new Error(`${label} failed validation: ${details}`);
}
const branchSchema = loadSchema('tf-branch.schema.json');
const planSchema = loadSchema('tf-plan.schema.json');
const compareSchema = loadSchema('tf-compare.schema.json');
export const tfSchemas = Object.freeze({
    branch: branchSchema,
    plan: planSchema,
    compare: compareSchema,
});
const ajv = new Ajv({ allErrors: true, strict: true });
ajv.addSchema(branchSchema, 'tf-branch.schema.json');
const validatePlanGraphFn = ajv.compile(planSchema);
const validatePlanNodeFn = ajv.compile(branchSchema);
const validateCompareFn = ajv.compile(compareSchema);
export function validateBranch(value) {
    return assertValid(value, validatePlanNodeFn, 'Plan node');
}
export function validatePlan(value) {
    const plan = assertValid(value, validatePlanGraphFn, 'Plan graph');
    plan.nodes.forEach((node) => {
        validateBranch(node);
    });
    return plan;
}
export function validateCompare(value) {
    return assertValid(value, validateCompareFn, 'Compare report');
}
