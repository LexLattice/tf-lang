import assert from 'node:assert/strict';

const BASE_KINDS = new Set(['int', 'float', 'string', 'bool', 'bytes', 'unit', 'any']);
const REFINEMENT_TAGS = new Set(['timestamp_ms', 'uri', 'digest_sha256', 'symbol', 'idempotency_key']);

function makeBase(name, refinements = []) {
  assert(BASE_KINDS.has(name), `unknown base kind: ${name}`);
  const tags = Array.from(new Set(refinements));
  tags.sort();
  return { kind: 'base', name, refinements: tags };
}

function cloneType(type) {
  switch (type.kind) {
    case 'base':
      return makeBase(type.name, type.refinements);
    case 'array':
      return { kind: 'array', type: cloneType(type.type) };
    case 'option':
      return { kind: 'option', type: cloneType(type.type) };
    case 'object': {
      const entries = Object.entries(type.shape);
      const shape = {};
      for (const [key, field] of entries) {
        shape[key] = { type: cloneType(field.type), optional: !!field.optional };
      }
      return { kind: 'object', shape };
    }
    case 'union':
      return {
        kind: 'union',
        types: type.types.map((member) => cloneType(member)),
      };
    default:
      throw new Error(`unknown type kind: ${type.kind}`);
  }
}

function int() {
  return makeBase('int');
}

function float() {
  return makeBase('float');
}

function string() {
  return makeBase('string');
}

function bool() {
  return makeBase('bool');
}

function bytes() {
  return makeBase('bytes');
}

function unit() {
  return makeBase('unit');
}

function any() {
  return makeBase('any');
}

function array(type) {
  return { kind: 'array', type: cloneType(type) };
}

function option(type) {
  return { kind: 'option', type: cloneType(type) };
}

function normalizeFieldSpec(spec) {
  if (spec && typeof spec === 'object' && 'type' in spec) {
    return { type: cloneType(spec.type), optional: !!spec.optional };
  }
  return { type: cloneType(spec), optional: false };
}

function object(shape) {
  assert(shape && typeof shape === 'object' && !Array.isArray(shape), 'object shape must be an object');
  const keys = Object.keys(shape).sort();
  const normalized = {};
  for (const key of keys) {
    normalized[key] = normalizeFieldSpec(shape[key]);
  }
  return { kind: 'object', shape: normalized };
}

function flattenUnionArgs(args) {
  const flat = [];
  for (const entry of args) {
    if (Array.isArray(entry)) {
      flat.push(...flattenUnionArgs(entry));
    } else if (entry && entry.kind === 'union') {
      flat.push(...entry.types.map((t) => cloneType(t)));
    } else if (entry) {
      flat.push(cloneType(entry));
    }
  }
  return flat;
}

function canonicalize(value) {
  if (Array.isArray(value)) {
    return value.map((item) => canonicalize(item));
  }
  if (value && typeof value === 'object') {
    const entries = Object.entries(value).sort(([a], [b]) => a.localeCompare(b));
    const out = {};
    for (const [key, val] of entries) {
      out[key] = canonicalize(val);
    }
    return out;
  }
  return value;
}

function toJSON(type) {
  switch (type.kind) {
    case 'base': {
      if (type.refinements.length === 0) {
        return { [type.name]: true };
      }
      return { refined: [type.name, ...type.refinements] };
    }
    case 'array':
      return { array: toJSON(type.type) };
    case 'option':
      return { option: toJSON(type.type) };
    case 'object': {
      const entries = Object.entries(type.shape).sort(([a], [b]) => a.localeCompare(b));
      const shape = entries.map(([key, field]) => {
        const item = { key, type: toJSON(field.type) };
        if (field.optional) {
          item.optional = true;
        }
        return item;
      });
      return { object: { shape } };
    }
    case 'union': {
      const members = type.types.map((member) => canonicalize(toJSON(member)));
      members.sort((a, b) => canonicalJSONStringify(a).localeCompare(canonicalJSONStringify(b)));
      return { union: members };
    }
    default:
      throw new Error(`cannot serialise type of kind: ${type.kind}`);
  }
}

function canonicalJSONStringify(value) {
  return JSON.stringify(canonicalize(value));
}

function canonicalJSONStringifyType(type) {
  return canonicalJSONStringify(toJSON(type));
}

function fromJSON(json) {
  assert(json && typeof json === 'object' && !Array.isArray(json), 'type JSON must be an object');
  const keys = Object.keys(json);
  assert(keys.length === 1, 'type JSON must have exactly one key');
  const key = keys[0];
  switch (key) {
    case 'int':
    case 'float':
    case 'string':
    case 'bool':
    case 'bytes':
    case 'unit':
    case 'any':
      return makeBase(key);
    case 'refined': {
      const data = json.refined;
      assert(Array.isArray(data) && data.length >= 2, 'refined expects [base, ...tags]');
      const [baseName, ...tags] = data;
      assert(typeof baseName === 'string', 'refined base must be a string kind name');
      for (const tag of tags) {
        assert(typeof tag === 'string', 'refinement tag must be a string');
      }
      return makeBase(baseName, tags);
    }
    case 'array':
      return array(fromJSON(json.array));
    case 'option':
      return option(fromJSON(json.option));
    case 'object': {
      const shape = json.object?.shape;
      assert(Array.isArray(shape), 'object.shape must be an array');
      const entries = shape.map((item) => {
        assert(item && typeof item === 'object', 'shape entries must be objects');
        const { key: fieldKey, type: fieldType, optional = false } = item;
        assert(typeof fieldKey === 'string', 'shape key must be a string');
        return [fieldKey, { type: fromJSON(fieldType), optional: !!optional }];
      });
      const obj = {};
      for (const [fieldKey, fieldSpec] of entries) {
        obj[fieldKey] = fieldSpec;
      }
      return { kind: 'object', shape: obj };
    }
    case 'union': {
      const members = json.union;
      assert(Array.isArray(members) && members.length > 0, 'union must be a non-empty array');
      const parsed = members.map((member) => fromJSON(member));
      return union(parsed);
    }
    default:
      throw new Error(`unknown type token: ${key}`);
  }
}

function dedupeUnionMembers(members) {
  const map = new Map();
  for (const member of members) {
    const key = canonicalJSONStringifyType(member);
    if (!map.has(key)) {
      map.set(key, member);
    }
  }
  return Array.from(map.values()).sort((a, b) => {
    const sa = canonicalJSONStringifyType(a);
    const sb = canonicalJSONStringifyType(b);
    return sa.localeCompare(sb);
  });
}

function union(...members) {
  const flat = flattenUnionArgs(members);
  assert(flat.length >= 1, 'union requires at least one member');
  const deduped = dedupeUnionMembers(flat);
  return { kind: 'union', types: deduped };
}

function refined(type, tag) {
  assert(typeof tag === 'string', 'refinement tag must be a string');
  assert(REFINEMENT_TAGS.has(tag), `unsupported refinement tag: ${tag}`);
  const base = cloneType(type);
  assert(base.kind === 'base', 'refined() currently supports base kinds only');
  const existing = new Set(base.refinements);
  existing.add(tag);
  return makeBase(base.name, Array.from(existing));
}

function combineRefinements(name, a, b) {
  const setA = new Set(a);
  const setB = new Set(b);
  if (setA.size === 0 && setB.size === 0) {
    return makeBase(name);
  }
  const intersection = Array.from(setA).filter((tag) => setB.has(tag));
  if (intersection.length === 0) {
    return null;
  }
  return makeBase(name, intersection);
}

function unify(a, b) {
  const left = cloneType(a);
  const right = cloneType(b);
  if (left.kind === 'base' && left.name === 'any') {
    return { ok: true, type: right };
  }
  if (right.kind === 'base' && right.name === 'any') {
    return { ok: true, type: left };
  }
  if (left.kind === 'union' || right.kind === 'union') {
    const members = [];
    if (left.kind === 'union') {
      members.push(...left.types);
    } else {
      members.push(left);
    }
    if (right.kind === 'union') {
      members.push(...right.types);
    } else {
      members.push(right);
    }
    return { ok: true, type: union(members) };
  }
  if (left.kind !== right.kind) {
    if (left.kind === 'object' || right.kind === 'object') {
      return { ok: false, reason: 'shape_mismatch' };
    }
    if (left.kind === 'base' && right.kind === 'base' && (left.name === 'string' && right.name === 'bytes' || left.name === 'bytes' && right.name === 'string')) {
      return { ok: false, reason: 'kind_mismatch' };
    }
    return { ok: false, reason: 'kind_mismatch' };
  }
  switch (left.kind) {
    case 'base':
      if (left.name !== right.name) {
        return { ok: false, reason: 'kind_mismatch' };
      }
      if ((left.name === 'string' && right.name === 'bytes') || (left.name === 'bytes' && right.name === 'string')) {
        return { ok: false, reason: 'kind_mismatch' };
      }
      const combined = combineRefinements(left.name, left.refinements, right.refinements);
      if (!combined) {
        return { ok: false, reason: 'refinement_mismatch' };
      }
      return { ok: true, type: combined };
    case 'array': {
      const unified = unify(left.type, right.type);
      if (!unified.ok) {
        return unified;
      }
      return { ok: true, type: array(unified.type) };
    }
    case 'option': {
      const unified = unify(left.type, right.type);
      if (!unified.ok) {
        return unified;
      }
      return { ok: true, type: option(unified.type) };
    }
    case 'object': {
      const keysLeft = Object.keys(left.shape);
      const keysRight = Object.keys(right.shape);
      const shared = keysLeft.filter((key) => keysRight.includes(key));
      if (shared.length === 0) {
        return { ok: false, reason: 'shape_mismatch' };
      }
      const resultShape = {};
      for (const key of shared) {
        const unified = unify(left.shape[key].type, right.shape[key].type);
        if (!unified.ok) {
          return unified;
        }
        resultShape[key] = {
          type: unified.type,
          optional: left.shape[key].optional || right.shape[key].optional,
        };
      }
      return { ok: true, type: object(resultShape) };
    }
    default:
      throw new Error(`unify not implemented for kind: ${left.kind}`);
  }
}

export {
  any,
  array,
  bool,
  bytes,
  canonicalJSONStringifyType,
  float,
  fromJSON,
  int,
  object,
  option,
  refined,
  string,
  toJSON,
  union,
  unit,
  unify,
};

