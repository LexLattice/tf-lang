const BASE_KINDS = new Set([
  "int",
  "float",
  "string",
  "bool",
  "bytes",
  "unit",
  "any"
]);

const REFINEMENT_TAGS = new Set([
  "timestamp_ms",
  "uri",
  "digest_sha256",
  "symbol",
  "idempotency_key"
]);

function createBase(kind, refinements = []) {
  if (!BASE_KINDS.has(kind)) {
    throw new Error(`unknown base kind: ${kind}`);
  }
  if (kind === "any" && refinements.length > 0) {
    throw new Error("cannot refine 'any'");
  }
  const unique = Array.from(new Set(refinements));
  unique.sort();
  return {
    kind: "base",
    name: kind,
    refinements: unique
  };
}

function cloneBase(type) {
  return createBase(type.name, type.refinements ?? []);
}

function baseFactory(kind) {
  return () => createBase(kind);
}

export const int = baseFactory("int");
export const float = baseFactory("float");
export const string = baseFactory("string");
export const bool = baseFactory("bool");
export const bytes = baseFactory("bytes");
export const unit = baseFactory("unit");
export const any = baseFactory("any");

export function kind(name) {
  return createBase(name);
}

export function refined(type, tag) {
  if (!REFINEMENT_TAGS.has(tag)) {
    throw new Error(`unknown refinement tag: ${tag}`);
  }
  const normalized = normalize(type);
  if (normalized.kind !== "base") {
    throw new Error("refinements are only supported on base kinds");
  }
  const tags = new Set(normalized.refinements);
  tags.add(tag);
  return createBase(normalized.name, Array.from(tags));
}

export function array(type) {
  return {
    kind: "array",
    element: normalize(type)
  };
}

export function option(type) {
  return {
    kind: "option",
    inner: normalize(type)
  };
}

function normalizeField(key, descriptor) {
  let optional = false;
  let cleanKey = key;
  if (cleanKey.endsWith("?")) {
    optional = true;
    cleanKey = cleanKey.slice(0, -1);
  }

  let typeDescriptor = descriptor;
  if (descriptor && typeof descriptor === "object" && "type" in descriptor) {
    typeDescriptor = descriptor.type;
    if (descriptor.optional !== undefined) {
      optional = Boolean(descriptor.optional);
    }
  }

  return {
    key: cleanKey,
    optional,
    type: normalize(typeDescriptor)
  };
}

function makeObjectFromFields(fields) {
  const mapped = fields.map((field) => ({
    key: field.key,
    optional: Boolean(field.optional),
    type: normalize(field.type)
  }));
  mapped.sort((a, b) => a.key.localeCompare(b.key));
  return {
    kind: "object",
    fields: mapped
  };
}

export function object(shape) {
  if (!shape || typeof shape !== "object" || Array.isArray(shape)) {
    throw new Error("object() expects a plain object shape");
  }
  const entries = Object.entries(shape).map(([key, descriptor]) =>
    normalizeField(key, descriptor)
  );
  const seen = new Set();
  for (const field of entries) {
    if (seen.has(field.key)) {
      throw new Error(`duplicate field '${field.key}' in object shape`);
    }
    seen.add(field.key);
  }
  return makeObjectFromFields(entries);
}

function flattenUnion(types) {
  const queue = [];
  for (const candidate of types) {
    const normalized = normalize(candidate);
    if (normalized.kind === "union") {
      queue.push(...normalized.variants);
    } else {
      queue.push(normalized);
    }
  }
  const lookup = new Map();
  for (const variant of queue) {
    const key = canonicalStringify(toJSON(variant));
    lookup.set(key, variant);
  }
  const sortedKeys = Array.from(lookup.keys()).sort();
  return sortedKeys.map((key) => lookup.get(key));
}

export function union(...types) {
  if (types.length === 0) {
    throw new Error("union() requires at least one type");
  }
  const variants = flattenUnion(types);
  if (variants.length === 1) {
    return variants[0];
  }
  return {
    kind: "union",
    variants
  };
}

export function normalize(type) {
  if (!type || typeof type !== "object") {
    throw new Error("invalid type descriptor");
  }
  switch (type.kind) {
    case "base":
      return cloneBase(type);
    case "array":
      return array(type.element);
    case "option":
      return option(type.inner);
    case "object":
      return makeObjectFromFields(type.fields ?? []);
    case "union":
      return union(...(type.variants ?? []));
    default:
      throw new Error(`unsupported type descriptor: ${JSON.stringify(type)}`);
  }
}

function canonicalize(value) {
  if (Array.isArray(value)) {
    return value.map((entry) => canonicalize(entry));
  }
  if (value && typeof value === "object") {
    const result = {};
    const keys = Object.keys(value).sort();
    for (const key of keys) {
      result[key] = canonicalize(value[key]);
    }
    return result;
  }
  return value;
}

export function canonicalStringify(value) {
  return JSON.stringify(canonicalize(value));
}

export function toJSON(type) {
  const normalized = normalize(type);
  switch (normalized.kind) {
    case "base": {
      if (normalized.refinements.length === 0) {
        return { [normalized.name]: true };
      }
      const baseToken = normalized.name;
      if (normalized.refinements.length === 1) {
        return { refined: [baseToken, normalized.refinements[0]] };
      }
      return { refined: [baseToken, [...normalized.refinements]] };
    }
    case "array":
      return { array: toJSON(normalized.element) };
    case "option":
      return { option: toJSON(normalized.inner) };
    case "object": {
      const required = {};
      const optional = {};
      for (const field of normalized.fields) {
        const container = field.optional ? optional : required;
        container[field.key] = toJSON(field.type);
      }
      const payload = {};
      const requiredKeys = Object.keys(required);
      const optionalKeys = Object.keys(optional);
      if (requiredKeys.length > 0) {
        requiredKeys.sort();
        const obj = {};
        for (const key of requiredKeys) {
          obj[key] = required[key];
        }
        payload.required = obj;
      }
      if (optionalKeys.length > 0) {
        optionalKeys.sort();
        const obj = {};
        for (const key of optionalKeys) {
          obj[key] = optional[key];
        }
        payload.optional = obj;
      }
      return { object: payload };
    }
    case "union":
      return {
        union: normalized.variants.map((variant) => toJSON(variant))
      };
    default:
      throw new Error(`cannot convert to JSON: ${JSON.stringify(normalized)}`);
  }
}

export function fromJSON(json) {
  if (!json || typeof json !== "object" || Array.isArray(json)) {
    throw new Error("fromJSON expects an object");
  }
  if ("refined" in json) {
    const [baseToken, refinementSpec] = json.refined;
    const baseType = typeof baseToken === "string" ? kind(baseToken) : fromJSON(baseToken);
    const tags = Array.isArray(refinementSpec)
      ? refinementSpec
      : [refinementSpec];
    return tags.reduce((acc, tag) => refined(acc, tag), baseType);
  }
  if ("array" in json) {
    return array(fromJSON(json.array));
  }
  if ("option" in json) {
    return option(fromJSON(json.option));
  }
  if ("object" in json) {
    const payload = json.object;
    if (!payload || typeof payload !== "object" || Array.isArray(payload)) {
      throw new Error("object payload must be an object");
    }
    const shape = {};
    if (payload.required) {
      for (const [key, value] of Object.entries(payload.required)) {
        shape[key] = fromJSON(value);
      }
    }
    if (payload.optional) {
      for (const [key, value] of Object.entries(payload.optional)) {
        shape[`${key}?`] = fromJSON(value);
      }
    }
    return object(shape);
  }
  if ("union" in json) {
    const variants = json.union.map((variant) => fromJSON(variant));
    return union(...variants);
  }
  const entries = Object.entries(json);
  if (entries.length === 1) {
    const [key, value] = entries[0];
    if (value === true && BASE_KINDS.has(key)) {
      return kind(key);
    }
  }
  throw new Error(`unsupported JSON payload: ${JSON.stringify(json)}`);
}

function cloneObjectFields(fields) {
  return fields.map((field) => ({
    key: field.key,
    optional: field.optional,
    type: normalize(field.type)
  }));
}

function makeObjectType(fields) {
  return makeObjectFromFields(cloneObjectFields(fields));
}

function isAny(type) {
  return type.kind === "base" && type.name === "any";
}

function kindMismatchReason(a, b) {
  if (a.kind === "object" || b.kind === "object") {
    return "shape_mismatch";
  }
  return "kind_mismatch";
}

export function unify(left, right) {
  const a = normalize(left);
  const b = normalize(right);

  if (isAny(a)) {
    return { ok: true, type: b };
  }
  if (isAny(b)) {
    return { ok: true, type: a };
  }

  if (a.kind === "union" || b.kind === "union") {
    const variants = [];
    if (a.kind === "union") variants.push(...a.variants);
    else variants.push(a);
    if (b.kind === "union") variants.push(...b.variants);
    else variants.push(b);
    return { ok: true, type: union(...variants) };
  }

  if (a.kind !== b.kind) {
    return { ok: false, reason: kindMismatchReason(a, b) };
  }

  switch (a.kind) {
    case "base": {
      if (a.name !== b.name) {
        return { ok: false, reason: "kind_mismatch" };
      }
      const leftTags = a.refinements;
      const rightTags = b.refinements;
      if (leftTags.length === 0 && rightTags.length === 0) {
        return { ok: true, type: createBase(a.name) };
      }
      if (leftTags.length === 0 || rightTags.length === 0) {
        return { ok: false, reason: "refinement_mismatch" };
      }
      const intersection = leftTags.filter((tag) => rightTags.includes(tag));
      if (intersection.length === 0) {
        return { ok: false, reason: "refinement_mismatch" };
      }
      return { ok: true, type: createBase(a.name, intersection) };
    }
    case "array": {
      const inner = unify(a.element, b.element);
      if (!inner.ok) {
        return inner;
      }
      return { ok: true, type: array(inner.type) };
    }
    case "option": {
      const inner = unify(a.inner, b.inner);
      if (!inner.ok) {
        return inner;
      }
      return { ok: true, type: option(inner.type) };
    }
    case "object": {
      if (a.fields.length !== b.fields.length) {
        return { ok: false, reason: "shape_mismatch" };
      }
      const merged = [];
      for (let i = 0; i < a.fields.length; i += 1) {
        const leftField = a.fields[i];
        const rightField = b.fields[i];
        if (leftField.key !== rightField.key || leftField.optional !== rightField.optional) {
          return { ok: false, reason: "shape_mismatch" };
        }
        const fieldResult = unify(leftField.type, rightField.type);
        if (!fieldResult.ok) {
          return fieldResult;
        }
        merged.push({
          key: leftField.key,
          optional: leftField.optional,
          type: fieldResult.type
        });
      }
      return { ok: true, type: makeObjectType(merged) };
    }
    default:
      throw new Error(`unhandled kind: ${a.kind}`);
  }
}

export const refinements = Object.freeze(Array.from(REFINEMENT_TAGS));
export const baseKinds = Object.freeze(Array.from(BASE_KINDS));
