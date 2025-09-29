import { isDeepStrictEqual } from 'node:util';
import { loadPrimitiveEffectMap } from './data.mjs';

const COMMUTE_EMIT_METRIC_LAW = 'commute:emit-metric-with-pure';
const INVERSE_SERIALIZE_DESERIALIZE_LAW = 'inverse:serialize-deserialize';
const IDEMPOTENT_HASH_LAW = 'idempotent:hash';

const HASH_PRIM = 'hash';
const EMIT_METRIC_PRIM = 'emit-metric';
const SERIALIZE_PRIM = 'serialize';
const DESERIALIZE_PRIM = 'deserialize';

let purePrimitiveSetPromise;

async function listPurePrimitiveNames() {
  if (!purePrimitiveSetPromise) {
    purePrimitiveSetPromise = (async () => {
      const effectMap = await loadPrimitiveEffectMap();
      const pureNames = new Set();
      for (const [name, effects] of effectMap.entries()) {
        if (!Array.isArray(effects)) {
          continue;
        }
        if (effects.some((effect) => String(effect).toLowerCase() === 'pure')) {
          pureNames.add(name);
        }
      }
      return pureNames;
    })();
  }
  return new Set(await purePrimitiveSetPromise);
}

export function canonicalPrimitiveName(value) {
  if (typeof value !== 'string') {
    return '';
  }
  const trimmed = value.trim().toLowerCase();
  if (!trimmed) {
    return '';
  }
  const afterSlash = trimmed.includes('/')
    ? trimmed.substring(trimmed.lastIndexOf('/') + 1)
    : trimmed;
  const beforeAt = afterSlash.includes('@')
    ? afterSlash.substring(0, afterSlash.indexOf('@'))
    : afterSlash;
  return beforeAt || trimmed;
}

export function extractPrimitivesFromIr(ir, acc = []) {
  if (!ir || typeof ir !== 'object') {
    return acc;
  }

  if (ir.node === 'Prim') {
    const candidateKeys = ['prim', 'prim_id', 'primId', 'primID', 'id'];
    for (const key of candidateKeys) {
      if (typeof ir[key] === 'string') {
        const name = canonicalPrimitiveName(ir[key]);
        if (name) {
          acc.push({ name, node: ir });
          break;
        }
      }
    }
  }

  for (const value of Object.values(ir)) {
    if (Array.isArray(value)) {
      for (const item of value) {
        extractPrimitivesFromIr(item, acc);
      }
    } else if (value && typeof value === 'object') {
      extractPrimitivesFromIr(value, acc);
    }
  }

  return acc;
}

function isHashPair(a, b) {
  return a === HASH_PRIM && b === HASH_PRIM;
}

function isSerializeDeserializePair(a, b) {
  return a === SERIALIZE_PRIM && b === DESERIALIZE_PRIM;
}

function isEmitMetricPurePair(a, b, pureSet) {
  return a === EMIT_METRIC_PRIM && pureSet.has(b);
}

function toDescriptor(entry) {
  if (typeof entry === 'string') {
    const name = canonicalPrimitiveName(entry);
    return name ? { name } : null;
  }
  if (!entry || typeof entry !== 'object') {
    return null;
  }
  if (typeof entry.name === 'string') {
    const name = canonicalPrimitiveName(entry.name);
    if (!name) {
      return null;
    }
    const node = entry.node && typeof entry.node === 'object' ? entry.node : null;
    return node ? { name, node } : { name };
  }
  if (entry.node === 'Prim') {
    const candidateKeys = ['prim', 'prim_id', 'primId', 'primID', 'id'];
    for (const key of candidateKeys) {
      if (typeof entry[key] === 'string') {
        const name = canonicalPrimitiveName(entry[key]);
        if (name) {
          return { name, node: entry };
        }
      }
    }
  }
  return null;
}

function nodesEqual(a, b) {
  if (!a || !b) {
    return false;
  }
  if (a === b) {
    return true;
  }
  return isDeepStrictEqual(a, b);
}

export async function analyzePrimitiveSequence(seq) {
  const obligations = [];
  const lawSet = new Set();
  const pureSet = await listPurePrimitiveNames();
  const descriptors = [];

  for (const entry of seq || []) {
    const descriptor = toDescriptor(entry);
    if (descriptor) {
      descriptors.push(descriptor);
    }
  }

  for (let i = 1; i < descriptors.length; i += 1) {
    const prev = descriptors[i - 1];
    const curr = descriptors[i];
    const prevName = prev.name;
    const currName = curr.name;
    if (isEmitMetricPurePair(prevName, currName, pureSet)) {
      obligations.push({
        law: COMMUTE_EMIT_METRIC_LAW,
        span: [i - 1, i],
        primitives: [prevName, currName],
      });
      lawSet.add(COMMUTE_EMIT_METRIC_LAW);
      continue;
    }
    if (isSerializeDeserializePair(prevName, currName)) {
      obligations.push({
        law: INVERSE_SERIALIZE_DESERIALIZE_LAW,
        span: [i - 1, i],
        primitives: [prevName, currName],
      });
      lawSet.add(INVERSE_SERIALIZE_DESERIALIZE_LAW);
      continue;
    }
    if (isHashPair(prevName, currName) && nodesEqual(prev.node, curr.node)) {
      obligations.push({
        law: IDEMPOTENT_HASH_LAW,
        span: [i - 1, i],
        primitives: [prevName, currName],
      });
      lawSet.add(IDEMPOTENT_HASH_LAW);
    }
  }

  return {
    primitives: descriptors.map((descriptor) => descriptor.name),
    obligations,
    rewritesApplied: obligations.length,
    laws: Array.from(lawSet).sort(),
  };
}
