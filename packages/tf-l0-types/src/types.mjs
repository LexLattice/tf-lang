import assert from 'node:assert/strict';

const BASE_KINDS = new Set(['int', 'float', 'string', 'bool', 'bytes', 'unit', 'any']);
const REFINEMENT_TAGS = new Set([
  'timestamp_ms',
  'uri',
  'digest_sha256',
  'symbol',
  'idempotency_key'
]);
const CANONICAL_SORT = Symbol('tf:canonical:sort');

function normalizeRefinements(refinements = []) {
  const tags = Array.from(new Set(refinements));
  tags.forEach((tag) => {
    if (!REFINEMENT_TAGS.has(tag)) {
      throw new Error(`unknown refinement tag: ${tag}`);
    }
  });
  tags.sort();
  return tags;
}

function baseKind(kind, refinements = []) {
  if (!BASE_KINDS.has(kind)) {
    throw new Error(`unknown kind: ${kind}`);
  }
  const normalRefinements = normalizeRefinements(refinements);
  return freezeType({ kind, refinements: normalRefinements });
}

function freezeType(type) {
  switch (type.kind) {
    case 'array':
      return Object.freeze({ kind: 'array', items: type.items });
    case 'option':
      return Object.freeze({ kind: 'option', inner: type.inner });
    case 'object': {
      const frozenFields = {};
      for (const [name, field] of Object.entries(type.fields)) {
        frozenFields[name] = Object.freeze({ type: field.type, optional: field.optional });
      }
      return Object.freeze({ kind: 'object', fields: Object.freeze(frozenFields) });
    }
    case 'union': {
      const variants = type.variants.slice();
      Object.freeze(variants);
      return Object.freeze({ kind: 'union', variants });
    }
    default: {
      if (!BASE_KINDS.has(type.kind)) {
        throw new Error(`cannot freeze unknown kind: ${type.kind}`);
      }
      return Object.freeze({ kind: type.kind, refinements: type.refinements.slice() });
    }
  }
}

export const int = baseKind('int');
export const float = baseKind('float');
export const string = baseKind('string');
export const bool = baseKind('bool');
export const bytes = baseKind('bytes');
export const unit = baseKind('unit');
export const any = baseKind('any');

function assertType(value) {
  assert.ok(value && typeof value === 'object', 'expected type object');
  assert.ok(typeof value.kind === 'string', 'type missing kind');
}

function cloneBase(type) {
  return { kind: type.kind, refinements: type.refinements.slice() };
}

function makeObject(fieldsMap) {
  const normal = {};
  for (const [name, field] of Object.entries(fieldsMap)) {
    assertType(field.type);
    normal[name] = { type: field.type, optional: Boolean(field.optional) };
  }
  return freezeType({ kind: 'object', fields: normal });
}

export function array(inner) {
  assertType(inner);
  return freezeType({ kind: 'array', items: inner });
}

export function option(inner) {
  assertType(inner);
  return freezeType({ kind: 'option', inner });
}

export function object(shape) {
  if (!shape || typeof shape !== 'object') {
    throw new Error('object shape must be an object');
  }
  const fields = {};
  for (const [rawKey, descriptor] of Object.entries(shape)) {
    let key = rawKey;
    let optional = false;
    if (key.endsWith('?')) {
      optional = true;
      key = key.slice(0, -1);
    }
    if (!key) {
      throw new Error('empty field name');
    }
    if (fields[key]) {
      throw new Error(`duplicate field: ${key}`);
    }
    let typeDescriptor = descriptor;
    if (descriptor && typeof descriptor === 'object' && 'type' in descriptor) {
      typeDescriptor = descriptor.type;
      if ('optional' in descriptor) {
        optional = Boolean(descriptor.optional);
      }
    }
    assertType(typeDescriptor);
    fields[key] = { type: typeDescriptor, optional };
  }
  return makeObject(fields);
}

function dedupeAndSortTypes(types) {
  const map = new Map();
  for (const type of types) {
    assertType(type);
    const key = canonicalTypeKey(type);
    if (!map.has(key)) {
      map.set(key, type);
    }
  }
  return Array.from(map.entries())
    .sort((a, b) => a[0].localeCompare(b[0]))
    .map(([, type]) => type);
}

function makeUnionType(types) {
  const variants = dedupeAndSortTypes(types);
  if (variants.length === 0) {
    throw new Error('union requires at least one variant');
  }
  if (variants.length === 1) {
    return variants[0];
  }
  return freezeType({ kind: 'union', variants });
}

export function union(...types) {
  const all = [];
  for (const type of types) {
    assertType(type);
    if (type.kind === 'union') {
      all.push(...type.variants);
    } else {
      all.push(type);
    }
  }
  return makeUnionType(all);
}

export function refined(type, tag) {
  assertType(type);
  if (!REFINEMENT_TAGS.has(tag)) {
    throw new Error(`unknown refinement tag: ${tag}`);
  }
  if (!BASE_KINDS.has(type.kind)) {
    throw new Error('refined() only supports base kinds');
  }
  if (type.kind === 'any') {
    throw new Error('cannot refine "any"');
  }
  const base = cloneBase(type);
  const tags = new Set(base.refinements);
  tags.add(tag);
  return freezeType({ kind: base.kind, refinements: normalizeRefinements(Array.from(tags)) });
}

const ERROR_REASONS = new Set(['kind_mismatch', 'shape_mismatch', 'refinement_mismatch', 'union_conflict']);

function fail(reason) {
  if (!ERROR_REASONS.has(reason)) {
    throw new Error(`invalid failure reason: ${reason}`);
  }
  return { ok: false, reason };
}

function baseUnify(a, b) {
  if (a.refinements.length === 0 && b.refinements.length === 0) {
    return { ok: true, type: baseKind(a.kind) };
  }
  if (a.refinements.length !== b.refinements.length) {
    return fail('refinement_mismatch');
  }
  for (let i = 0; i < a.refinements.length; i += 1) {
    if (a.refinements[i] !== b.refinements[i]) {
      return fail('refinement_mismatch');
    }
  }
  return { ok: true, type: baseKind(a.kind, a.refinements) };
}

function unifyArrays(a, b) {
  const inner = unify(a.items, b.items);
  if (!inner.ok) {
    return inner;
  }
  return { ok: true, type: array(inner.type) };
}

function unifyOptions(a, b) {
  const inner = unify(a.inner, b.inner);
  if (!inner.ok) {
    return inner;
  }
  return { ok: true, type: option(inner.type) };
}

function unifyObjects(a, b) {
  const sharedKeys = Object.keys(a.fields).filter((key) => key in b.fields);
  if (sharedKeys.length === 0) {
    return fail('shape_mismatch');
  }
  for (const [name, field] of Object.entries(a.fields)) {
    if (!(name in b.fields) && !field.optional) {
      return fail('shape_mismatch');
    }
  }
  for (const [name, field] of Object.entries(b.fields)) {
    if (!(name in a.fields) && !field.optional) {
      return fail('shape_mismatch');
    }
  }
  const resultFields = {};
  const sortedShared = sharedKeys.sort();
  for (const name of sortedShared) {
    const unified = unify(a.fields[name].type, b.fields[name].type);
    if (!unified.ok) {
      return unified;
    }
    const optional = a.fields[name].optional && b.fields[name].optional;
    resultFields[name] = {
      type: unified.type,
      optional,
    };
  }
  return { ok: true, type: makeObject(resultFields) };
}

function unifyUnions(a, b) {
  const left = a.kind === 'union' ? a.variants : [a];
  const right = b.kind === 'union' ? b.variants : [b];
  const results = [];
  for (const variantA of left) {
    for (const variantB of right) {
      const unified = unify(variantA, variantB);
      if (unified.ok) {
        results.push(unified.type);
      }
    }
  }
  if (results.length === 0) {
    return fail('union_conflict');
  }
  const combined = makeUnionType(results);
  return { ok: true, type: combined };
}

export function unify(a, b) {
  assertType(a);
  assertType(b);
  if (a.kind === 'any') {
    return { ok: true, type: b };
  }
  if (b.kind === 'any') {
    return { ok: true, type: a };
  }
  if (a.kind === 'union' || b.kind === 'union') {
    return unifyUnions(a, b);
  }
  if (a.kind !== b.kind) {
    return fail('kind_mismatch');
  }
  switch (a.kind) {
    case 'array':
      return unifyArrays(a, b);
    case 'option':
      return unifyOptions(a, b);
    case 'object':
      return unifyObjects(a, b);
    default:
      return baseUnify(a, b);
  }
}

function canonicalTypeKey(type) {
  return canonicalStringify(toJSON(type));
}

function encodeTypeJSON(type) {
  if (type.kind === 'union') {
    const variants = type.variants.map((variant) => encodeTypeJSON(variant));
    const marked = markUnorderedArray(variants);
    return { union: marked };
  }
  if (type.kind === 'array') {
    return { array: encodeTypeJSON(type.items) };
  }
  if (type.kind === 'option') {
    return { option: encodeTypeJSON(type.inner) };
  }
  if (type.kind === 'object') {
    const shape = {};
    const entries = Object.entries(type.fields).sort((a, b) => a[0].localeCompare(b[0]));
    for (const [name, field] of entries) {
      const key = field.optional ? `${name}?` : name;
      shape[key] = encodeTypeJSON(field.type);
    }
    return { object: shape };
  }
  if (type.refinements.length > 0) {
    return { refined: [type.kind, ...type.refinements] };
  }
  return { [type.kind]: true };
}

export function toJSON(type) {
  assertType(type);
  return normalizeCanonicalJSON(encodeTypeJSON(type));
}

export function fromJSON(json) {
  const payload = typeof json === 'string' ? JSON.parse(json) : json;
  if (!payload || typeof payload !== 'object') {
    throw new Error('fromJSON expects an object or JSON string');
  }
  const keys = Object.keys(payload);
  if (keys.length !== 1) {
    throw new Error('type JSON must contain exactly one top-level key');
  }
  const [key] = keys;
  switch (key) {
    case 'union': {
      const list = payload.union;
      if (!Array.isArray(list) || list.length === 0) {
        throw new Error('union expects non-empty array');
      }
      const variants = list.map((item) => fromJSON(item));
      return makeUnionType(variants);
    }
    case 'array':
      return array(fromJSON(payload.array));
    case 'option':
      return option(fromJSON(payload.option));
    case 'object': {
      const shape = payload.object;
      if (!shape || typeof shape !== 'object') {
        throw new Error('object expects shape object');
      }
      const fields = {};
      for (const [rawKey, value] of Object.entries(shape)) {
        let optional = false;
        let name = rawKey;
        if (name.endsWith('?')) {
          optional = true;
          name = name.slice(0, -1);
        }
        fields[name] = { type: fromJSON(value), optional };
      }
      return makeObject(fields);
    }
    case 'refined': {
      const list = payload.refined;
      if (!Array.isArray(list) || list.length < 2) {
        throw new Error('refined expects [base, ...tags]');
      }
      const [base, ...tags] = list;
      return baseKind(base, tags);
    }
    default: {
      if (!payload[key]) {
        throw new Error(`invalid type descriptor for ${key}`);
      }
      return baseKind(key);
    }
  }
}

function markUnorderedArray(values) {
  const copy = values.slice();
  Object.defineProperty(copy, CANONICAL_SORT, {
    value: true,
    enumerable: false,
    configurable: false,
    writable: false,
  });
  return copy;
}

function normalizeCanonicalJSON(value) {
  if (Array.isArray(value)) {
    const normalizedItems = value.map((item) => normalizeCanonicalJSON(item));
    if (value[CANONICAL_SORT]) {
      normalizedItems.sort((left, right) =>
        toCanonicalJSON(left).localeCompare(toCanonicalJSON(right))
      );
    }
    return normalizedItems;
  }
  if (value && typeof value === 'object') {
    const entries = Object.entries(value).sort((a, b) => a[0].localeCompare(b[0]));
    const normalized = {};
    for (const [key, child] of entries) {
      normalized[key] = normalizeCanonicalJSON(child);
    }
    return normalized;
  }
  return value;
}

export function toCanonicalJSON(value) {
  return JSON.stringify(normalizeCanonicalJSON(value));
}

export function canonicalStringify(value) {
  return toCanonicalJSON(value);
}

export function writeJSON(type) {
  return canonicalStringify(toJSON(type));
}

export const refinements = Array.from(REFINEMENT_TAGS).sort();
