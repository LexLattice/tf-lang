import { isDeepStrictEqual } from 'node:util';
import { canonicalPrimitiveName } from './rewrite-detect.mjs';

const COMMUTE_EMIT_METRIC_LAW = 'commute:emit-metric-with-pure';
const INVERSE_SERIALIZE_DESERIALIZE_LAW = 'inverse:serialize-deserialize';
const IDEMPOTENT_HASH_LAW = 'idempotent:hash';

const COMMUTE_TARGET = canonicalPrimitiveName('emit-metric');
const INVERSE_FIRST = canonicalPrimitiveName('serialize');
const INVERSE_SECOND = canonicalPrimitiveName('deserialize');
const IDEMPOTENT_TARGET = canonicalPrimitiveName('hash');

const PRIM_CANDIDATE_KEYS = ['prim', 'prim_id', 'primId', 'primID', 'id'];

function cloneIr(ir) {
  if (typeof structuredClone === 'function') {
    return structuredClone(ir);
  }
  return JSON.parse(JSON.stringify(ir));
}

function isPrimNode(node) {
  return Boolean(node && typeof node === 'object' && node.node === 'Prim');
}

function canonicalNodeName(node) {
  if (!isPrimNode(node)) {
    return '';
  }
  for (const key of PRIM_CANDIDATE_KEYS) {
    if (typeof node[key] === 'string') {
      const canonical = canonicalPrimitiveName(node[key]);
      if (canonical) {
        return canonical;
      }
    }
  }
  return '';
}

function traverseForPair(value, handler) {
  if (value == null) {
    return false;
  }
  if (Array.isArray(value)) {
    if (handler(value)) {
      return true;
    }
    for (const item of value) {
      if (traverseForPair(item, handler)) {
        return true;
      }
    }
    return false;
  }
  if (typeof value === 'object') {
    for (const val of Object.values(value)) {
      if (traverseForPair(val, handler)) {
        return true;
      }
    }
  }
  return false;
}

function applyCommuteOnce(ir, neighbors) {
  if (!neighbors || neighbors.size === 0) {
    return false;
  }
  return traverseForPair(ir, (arr) => {
    for (let i = 0; i < arr.length - 1; i += 1) {
      const left = arr[i];
      const right = arr[i + 1];
      if (!isPrimNode(left) || !isPrimNode(right)) {
        continue;
      }
      if (canonicalNodeName(left) === COMMUTE_TARGET && neighbors.has(canonicalNodeName(right))) {
        arr[i] = right;
        arr[i + 1] = left;
        return true;
      }
    }
    return false;
  });
}

function applyInverseOnce(ir) {
  return traverseForPair(ir, (arr) => {
    for (let i = 0; i < arr.length - 1; i += 1) {
      const left = arr[i];
      const right = arr[i + 1];
      if (!isPrimNode(left) || !isPrimNode(right)) {
        continue;
      }
      if (canonicalNodeName(left) === INVERSE_FIRST && canonicalNodeName(right) === INVERSE_SECOND) {
        arr.splice(i, 2);
        return true;
      }
    }
    return false;
  });
}

function applyIdempotentOnce(ir) {
  return traverseForPair(ir, (arr) => {
    for (let i = 0; i < arr.length - 1; i += 1) {
      const left = arr[i];
      const right = arr[i + 1];
      if (!isPrimNode(left) || !isPrimNode(right)) {
        continue;
      }
      if (canonicalNodeName(left) !== IDEMPOTENT_TARGET || canonicalNodeName(right) !== IDEMPOTENT_TARGET) {
        continue;
      }
      if (!isDeepStrictEqual(left, right)) {
        continue;
      }
      arr.splice(i + 1, 1);
      return true;
    }
    return false;
  });
}

export function applyRewritePlan(ir, obligations = []) {
  const workIr = cloneIr(ir);
  const usedLaws = new Set();
  let rewritesApplied = 0;

  const commuteNeighbors = new Set();
  let hasCommute = false;
  let hasInverse = false;
  let hasIdempotent = false;

  for (const obligation of obligations || []) {
    if (!obligation || typeof obligation !== 'object') {
      continue;
    }
    const { law } = obligation;
    if (law === COMMUTE_EMIT_METRIC_LAW) {
      hasCommute = true;
      if (Array.isArray(obligation.primitives) && obligation.primitives.length === 2) {
        const neighbor = canonicalPrimitiveName(obligation.primitives[1]);
        if (neighbor) {
          commuteNeighbors.add(neighbor);
        }
      }
      continue;
    }
    if (law === INVERSE_SERIALIZE_DESERIALIZE_LAW) {
      hasInverse = true;
      continue;
    }
    if (law === IDEMPOTENT_HASH_LAW) {
      hasIdempotent = true;
    }
  }

  let changed = false;
  do {
    changed = false;
    if (hasCommute && applyCommuteOnce(workIr, commuteNeighbors)) {
      rewritesApplied += 1;
      usedLaws.add(COMMUTE_EMIT_METRIC_LAW);
      changed = true;
    }
    if (hasInverse && applyInverseOnce(workIr)) {
      rewritesApplied += 1;
      usedLaws.add(INVERSE_SERIALIZE_DESERIALIZE_LAW);
      changed = true;
    }
    if (hasIdempotent && applyIdempotentOnce(workIr)) {
      rewritesApplied += 1;
      usedLaws.add(IDEMPOTENT_HASH_LAW);
      changed = true;
    }
  } while (changed);

  return {
    ir: workIr,
    rewritesApplied,
    usedLaws: Array.from(usedLaws).sort(),
  };
}

export { applyRewritePlan as applyObligations };

function normalizeValue(value) {
  if (Array.isArray(value)) {
    return value.map(normalizeValue);
  }
  if (value && typeof value === 'object') {
    const next = {};
    for (const key of Object.keys(value).sort()) {
      next[key] = normalizeValue(value[key]);
    }
    return next;
  }
  return value;
}

export function stableStringify(value) {
  return JSON.stringify(normalizeValue(value), null, 2);
}
