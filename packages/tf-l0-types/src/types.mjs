const BASE_KINDS = new Set([
  'int',
  'float',
  'string',
  'bool',
  'bytes',
  'unit',
  'any'
]);

const ALLOWED_REFINEMENTS = new Set([
  'timestamp_ms',
  'uri',
  'digest_sha256',
  'symbol',
  'idempotency_key'
]);

export function int() {
  return normalize({ kind: 'int' });
}

export function float() {
  return normalize({ kind: 'float' });
}

export function string() {
  return normalize({ kind: 'string' });
}

export function bool() {
  return normalize({ kind: 'bool' });
}

export function bytes() {
  return normalize({ kind: 'bytes' });
}

export function unit() {
  return normalize({ kind: 'unit' });
}

export function any() {
  return normalize({ kind: 'any' });
}

export function array(type) {
  const item = expectType(type, 'array');
  return normalize({ kind: 'array', items: item });
}

export function option(type) {
  const inner = expectType(type, 'option');
  return normalize({ kind: 'option', of: inner });
}

export function object(shape) {
  if (!shape || typeof shape !== 'object' || Array.isArray(shape)) {
    throw new TypeError('object() expects a shape object');
  }
  const fields = {};
  for (const name of Object.keys(shape)) {
    const spec = shape[name];
    let typeSpec;
    let optional = false;
    if (spec && typeof spec === 'object' && !Array.isArray(spec) && isTypeLike(spec.type)) {
      typeSpec = spec.type;
      optional = spec.optional === true;
    } else if (isTypeLike(spec)) {
      typeSpec = spec;
    } else {
      throw new TypeError(`object() field ${name} is not a type`);
    }
    fields[name] = {
      type: expectType(typeSpec, `object field ${name}`),
      optional
    };
  }
  return normalize({ kind: 'object', fields });
}

export function union(...types) {
  if (types.length === 0) {
    throw new TypeError('union() requires at least one type');
  }
  const collected = [];
  for (const type of types) {
    const normalized = normalize(expectType(type, 'union option'));
    if (normalized.kind === 'union') {
      collected.push(...normalized.options);
    } else {
      collected.push(normalized);
    }
  }
  const deduped = dedupeTypes(collected);
  if (deduped.length === 1) {
    return normalize(deduped[0]);
  }
  return normalize({ kind: 'union', options: deduped });
}

export function refined(type, tag) {
  if (!ALLOWED_REFINEMENTS.has(tag)) {
    throw new TypeError(`Unknown refinement tag: ${tag}`);
  }
  const base = normalize(expectType(type, 'refined base'));
  const next = { ...base, refinements: [...base.refinements, tag] };
  return normalize(next);
}

export function toJSON(type) {
  const normalized = normalize(expectType(type, 'toJSON'));
  return canonicalize(encodeTypeJSON(normalized));
}

export function fromJSON(json) {
  return decodeTypeJSON(json);
}

export function unify(left, right) {
  const a = normalize(expectType(left, 'unify left'));
  const b = normalize(expectType(right, 'unify right'));
  const result = unifyNormalized(a, b);
  if (result.ok) {
    return { ok: true, type: normalize(result.type) };
  }
  return result;
}

function expectType(value, context) {
  if (!isTypeLike(value)) {
    throw new TypeError(`${context} must be a type object`);
  }
  return value;
}

function isTypeLike(value) {
  return value && typeof value === 'object' && typeof value.kind === 'string';
}

function cloneType(type) {
  const copy = {
    kind: type.kind,
    refinements: Array.isArray(type.refinements) ? [...type.refinements] : []
  };
  switch (type.kind) {
    case 'array':
      copy.items = cloneType(type.items);
      break;
    case 'option':
      copy.of = cloneType(type.of);
      break;
    case 'object': {
      const fields = {};
      for (const name of Object.keys(type.fields || {})) {
        const field = type.fields[name];
        fields[name] = {
          optional: field.optional === true,
          type: cloneType(field.type)
        };
      }
      copy.fields = fields;
      break;
    }
    case 'union':
      copy.options = (type.options || []).map((opt) => cloneType(opt));
      break;
    default:
      if (!BASE_KINDS.has(type.kind)) {
        throw new TypeError(`Unknown type kind: ${type.kind}`);
      }
  }
  return copy;
}

function normalize(type) {
  return normalizeInPlace(cloneType(type));
}

function normalizeInPlace(type) {
  type.refinements = normalizeRefinements(type.refinements);
  switch (type.kind) {
    case 'array':
      type.items = normalizeInPlace(type.items);
      break;
    case 'option':
      type.of = normalizeInPlace(type.of);
      break;
    case 'object':
      type.fields = normalizeFields(type.fields);
      break;
    case 'union':
      type.options = normalizeUnionOptions(type.options);
      break;
    default:
      if (!BASE_KINDS.has(type.kind)) {
        throw new TypeError(`Unknown type kind: ${type.kind}`);
      }
  }
  return type;
}

function normalizeFields(fields = {}) {
  const result = {};
  const names = Object.keys(fields).sort();
  for (const name of names) {
    const field = fields[name];
    result[name] = {
      optional: field.optional === true,
      type: normalizeInPlace(field.type)
    };
  }
  return result;
}

function normalizeUnionOptions(options = []) {
  const flattened = [];
  for (const option of options) {
    const normalized = normalizeInPlace(option);
    if (normalized.kind === 'union') {
      flattened.push(...normalized.options);
    } else {
      flattened.push(normalized);
    }
  }
  const deduped = dedupeTypes(flattened);
  return deduped;
}

function dedupeTypes(types) {
  const seen = new Map();
  for (const type of types) {
    const key = canonicalString(type);
    if (!seen.has(key)) {
      seen.set(key, type);
    }
  }
  return Array.from(seen.entries())
    .sort((a, b) => a[0].localeCompare(b[0]))
    .map((entry) => entry[1]);
}

function normalizeRefinements(refs = []) {
  const seen = new Set();
  const result = [];
  for (const tag of refs) {
    if (!ALLOWED_REFINEMENTS.has(tag)) {
      throw new TypeError(`Unknown refinement tag: ${tag}`);
    }
    if (!seen.has(tag)) {
      seen.add(tag);
      result.push(tag);
    }
  }
  result.sort();
  return result;
}

function encodeTypeJSON(type) {
  let payload;
  switch (type.kind) {
    case 'array':
      payload = { array: encodeTypeJSON(type.items) };
      break;
    case 'option':
      payload = { option: encodeTypeJSON(type.of) };
      break;
    case 'object':
      payload = {
        object: {
          fields: Object.keys(type.fields)
            .sort()
            .map((name) => ({
              name,
              optional: type.fields[name].optional === true,
              type: encodeTypeJSON(type.fields[name].type)
            }))
        }
      };
      break;
    case 'union':
      payload = { union: type.options.map((opt) => encodeTypeJSON(opt)) };
      break;
    default: {
      if (!BASE_KINDS.has(type.kind)) {
        throw new TypeError(`Unknown type kind: ${type.kind}`);
      }
      payload = { [type.kind]: true };
    }
  }
  if (type.refinements.length > 0) {
    return {
      refined: [payload, ...type.refinements]
    };
  }
  return payload;
}

function decodeTypeJSON(json) {
  if (!json || typeof json !== 'object') {
    throw new TypeError('Type JSON must be an object');
  }
  if (Array.isArray(json)) {
    throw new TypeError('Type JSON must not be an array');
  }
  if (Object.prototype.hasOwnProperty.call(json, 'refined')) {
    const payload = json.refined;
    if (!Array.isArray(payload) || payload.length < 2) {
      throw new TypeError('refined expects [type, tag, ...]');
    }
    let result = decodeTypeJSON(payload[0]);
    for (const tag of payload.slice(1)) {
      if (typeof tag !== 'string') {
        throw new TypeError('refinement tag must be a string');
      }
      result = refined(result, tag);
    }
    return result;
  }
  const keys = Object.keys(json);
  if (keys.length !== 1) {
    throw new TypeError('Type JSON must have exactly one key');
  }
  const key = keys[0];
  switch (key) {
    case 'array':
      return array(decodeTypeJSON(json.array));
    case 'option':
      return option(decodeTypeJSON(json.option));
    case 'object':
      return object(decodeObjectFields(json.object));
    case 'union':
      if (!Array.isArray(json.union)) {
        throw new TypeError('union expects an array');
      }
      return union(...json.union.map((entry) => decodeTypeJSON(entry)));
    default:
      if (!BASE_KINDS.has(key)) {
        throw new TypeError(`Unknown kind in JSON: ${key}`);
      }
      if (json[key] !== true) {
        throw new TypeError(`Expected literal true for kind ${key}`);
      }
      return normalize({ kind: key });
  }
}

function decodeObjectFields(spec) {
  if (!spec || typeof spec !== 'object' || Array.isArray(spec)) {
    throw new TypeError('object.fields must be an object');
  }
  if (!Array.isArray(spec.fields)) {
    throw new TypeError('object.fields.fields must be an array');
  }
  const shape = {};
  for (const entry of spec.fields) {
    if (!entry || typeof entry !== 'object' || Array.isArray(entry)) {
      throw new TypeError('object field entry must be an object');
    }
    const { name, optional = false, type } = entry;
    if (typeof name !== 'string') {
      throw new TypeError('object field name must be a string');
    }
    shape[name] = { type: decodeTypeJSON(type), optional: optional === true };
  }
  return shape;
}

function canonicalize(value) {
  if (Array.isArray(value)) {
    return value.map((item) => canonicalize(item));
  }
  if (value && typeof value === 'object') {
    const result = {};
    for (const key of Object.keys(value).sort()) {
      result[key] = canonicalize(value[key]);
    }
    return result;
  }
  return value;
}

function canonicalString(type) {
  return stableStringify(encodeTypeJSON(type));
}

function stableStringify(value) {
  return JSON.stringify(canonicalize(value));
}

function unifyNormalized(a, b) {
  if (a.kind === 'any') {
    return { ok: true, type: cloneType(b) };
  }
  if (b.kind === 'any') {
    return { ok: true, type: cloneType(a) };
  }
  if (a.kind === 'union' || b.kind === 'union') {
    return unifyUnion(a, b);
  }
  if (a.kind !== b.kind) {
    return { ok: false, reason: 'kind_mismatch' };
  }
  switch (a.kind) {
    case 'array': {
      const element = unifyNormalized(a.items, b.items);
      if (!element.ok) {
        return element;
      }
      const refs = mergeRefinements(a.refinements, b.refinements);
      if (!refs) {
        return { ok: false, reason: 'refinement_mismatch' };
      }
      return {
        ok: true,
        type: {
          kind: 'array',
          items: element.type,
          refinements: refs
        }
      };
    }
    case 'option': {
      const inner = unifyNormalized(a.of, b.of);
      if (!inner.ok) {
        return inner;
      }
      const refs = mergeRefinements(a.refinements, b.refinements);
      if (!refs) {
        return { ok: false, reason: 'refinement_mismatch' };
      }
      return {
        ok: true,
        type: {
          kind: 'option',
          of: inner.type,
          refinements: refs
        }
      };
    }
    case 'object':
      return unifyObjects(a, b);
    default: {
      const refs = mergeRefinements(a.refinements, b.refinements);
      if (!refs) {
        return { ok: false, reason: 'refinement_mismatch' };
      }
      return { ok: true, type: { kind: a.kind, refinements: refs } };
    }
  }
}

function unifyObjects(a, b) {
  const keysA = Object.keys(a.fields);
  const keysB = Object.keys(b.fields);
  if (keysA.length !== keysB.length) {
    return { ok: false, reason: 'shape_mismatch' };
  }
  for (const key of keysA) {
    if (!Object.prototype.hasOwnProperty.call(b.fields, key)) {
      return { ok: false, reason: 'shape_mismatch' };
    }
  }
  const refs = mergeRefinements(a.refinements, b.refinements);
  if (!refs) {
    return { ok: false, reason: 'refinement_mismatch' };
  }
  const resultFields = {};
  for (const key of keysA.sort()) {
    const fieldA = a.fields[key];
    const fieldB = b.fields[key];
    if (fieldA.optional !== fieldB.optional) {
      return { ok: false, reason: 'shape_mismatch' };
    }
    const unified = unifyNormalized(fieldA.type, fieldB.type);
    if (!unified.ok) {
      return unified;
    }
    resultFields[key] = {
      optional: fieldA.optional,
      type: unified.type
    };
  }
  return {
    ok: true,
    type: {
      kind: 'object',
      fields: resultFields,
      refinements: refs
    }
  };
}

function unifyUnion(a, b) {
  const optionsA = a.kind === 'union' ? a.options : [a];
  const optionsB = b.kind === 'union' ? b.options : [b];
  const successes = [];
  for (const optA of optionsA) {
    for (const optB of optionsB) {
      const attempt = unifyNormalized(optA, optB);
      if (attempt.ok) {
        successes.push(attempt.type);
      }
    }
  }
  if (successes.length === 0) {
    return { ok: false, reason: 'union_mismatch' };
  }
  const unionType = union(...successes);
  const normalizedUnion = normalize(unionType);
  const finalRefs = mergeUnionRefinements(normalizedUnion.refinements, a.refinements, b.refinements);
  if (!finalRefs) {
    return { ok: false, reason: 'refinement_mismatch' };
  }
  normalizedUnion.refinements = finalRefs;
  return { ok: true, type: normalizedUnion };
}

function mergeUnionRefinements(existing, refsA = [], refsB = []) {
  const a = normalizeRefinements(refsA);
  const b = normalizeRefinements(refsB);
  let constraint = [];
  if (a.length > 0 && b.length > 0) {
    const merged = mergeRefinements(a, b);
    if (merged === null) {
      return null;
    }
    constraint = merged;
  } else if (a.length > 0) {
    constraint = a;
  } else if (b.length > 0) {
    constraint = b;
  }

  const base = Array.isArray(existing) ? normalizeRefinements(existing) : [];
  if (constraint.length === 0) {
    return base;
  }
  if (base.length === 0) {
    return normalizeRefinements(constraint);
  }
  const set = new Set(constraint);
  const intersection = base.filter((tag) => set.has(tag));
  if (intersection.length === 0) {
    return null;
  }
  return normalizeRefinements(intersection);
}

function mergeRefinements(left = [], right = []) {
  const a = normalizeRefinements(left);
  const b = normalizeRefinements(right);
  if (a.length === 0 && b.length === 0) {
    return [];
  }
  if (a.length === 0 || b.length === 0) {
    return null;
  }
  const setB = new Set(b);
  const intersection = a.filter((tag) => setB.has(tag));
  if (intersection.length === 0) {
    return null;
  }
  return normalizeRefinements(intersection);
}
