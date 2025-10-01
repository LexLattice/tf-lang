import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const DEFAULT_REGISTRY_PATH = path.resolve(__dirname, '../../adapters/registry.json');
const REPO_ROOT = path.resolve(__dirname, '..', '..');
const TRANSFORM_MODULE_PATH = path.resolve(REPO_ROOT, 'packages/transform/index.mjs');

export function formatPortPath(segments = []) {
  const parts = ['in'];
  for (const segment of segments ?? []) {
    if (typeof segment === 'number') {
      parts.push(String(segment));
    } else if (segment !== undefined && segment !== null) {
      parts.push(String(segment));
    }
  }
  return parts.join('.');
}

function stableStringify(value) {
  if (value === null) {
    return 'null';
  }
  if (typeof value !== 'object') {
    return JSON.stringify(value);
  }
  if (Array.isArray(value)) {
    return `[${value.map((item) => stableStringify(item)).join(',')}]`;
  }
  const keys = Object.keys(value).sort((a, b) => a.localeCompare(b));
  return `{${keys.map((key) => `${JSON.stringify(key)}:${stableStringify(value[key])}`).join(',')}}`;
}

function normalizeDescriptor(descriptor) {
  if (!descriptor || typeof descriptor !== 'object' || Array.isArray(descriptor)) {
    return null;
  }
  const schemaRef = descriptor.schemaRef;
  if (typeof schemaRef !== 'string' || schemaRef.length === 0) {
    return null;
  }
  const normalized = { schemaRef };
  normalized.format = descriptor.format ?? null;
  for (const [key, value] of Object.entries(descriptor)) {
    if (key === 'schemaRef' || key === 'format') {
      continue;
    }
    if (value !== undefined) {
      normalized[key] = value;
    }
  }
  return normalized;
}

function descriptorsEqual(a, b) {
  const left = normalizeDescriptor(a);
  const right = normalizeDescriptor(b);
  if (!left || !right) {
    return false;
  }
  return stableStringify(left) === stableStringify(right);
}

function formatTypeDescriptor(descriptor) {
  const normalized = normalizeDescriptor(descriptor);
  if (!normalized) {
    return 'unknown';
  }
  let result = normalized.schemaRef;
  if (normalized.format) {
    result += ` (${normalized.format})`;
  }
  const extras = Object.entries(normalized)
    .filter(([key]) => key !== 'schemaRef' && key !== 'format')
    .sort(([a], [b]) => a.localeCompare(b));
  if (extras.length > 0) {
    const extraText = extras
      .map(([key, value]) => `${key}=${JSON.stringify(value)}`)
      .join(', ');
    result += ` {${extraText}}`;
  }
  return result;
}

function sanitizeSegment(value) {
  return String(value ?? 'any')
    .replace(/[^A-Za-z0-9]+/g, '_')
    .replace(/^_+|_+$/g, '')
    .toLowerCase() || 'any';
}

function descriptorSlug(descriptor) {
  const normalized = normalizeDescriptor(descriptor);
  if (!normalized) {
    return 'unknown';
  }
  const parts = [normalized.schemaRef ?? 'unknown'];
  if (normalized.format) {
    parts.push(normalized.format);
  }
  const extras = Object.entries(normalized)
    .filter(([key]) => key !== 'schemaRef' && key !== 'format')
    .sort(([a], [b]) => a.localeCompare(b))
    .map(([key, value]) => `${key}-${value}`);
  for (const extra of extras) {
    parts.push(extra);
  }
  return parts.map(sanitizeSegment).join('_');
}

function opNameForAdapter(from, to) {
  const left = descriptorSlug(from);
  const right = descriptorSlug(to);
  return `adapter.${left}_to_${right}`;
}

function relativeImportPath(fromDir, targetFile) {
  let relative = path.relative(fromDir, targetFile).replace(/\\/g, '/');
  if (!relative.startsWith('.')) {
    relative = `./${relative}`;
  }
  return relative;
}

async function fileExists(filePath) {
  try {
    await fs.access(filePath);
    return true;
  } catch {
    return false;
  }
}

async function loadAdapterRegistry(registryPath = DEFAULT_REGISTRY_PATH) {
  try {
    const raw = await fs.readFile(registryPath, 'utf8');
    const parsed = JSON.parse(raw);
    if (!parsed || !Array.isArray(parsed.adapters)) {
      return [];
    }
    return parsed.adapters
      .map((entry) => ({
        id: entry.id ?? null,
        op: entry.op ?? null,
        from: normalizeDescriptor(entry.from),
        to: normalizeDescriptor(entry.to),
        description: typeof entry.description === 'string' ? entry.description : null,
      }))
      .filter((entry) => entry.op && entry.from && entry.to);
  } catch (error) {
    if (error?.code === 'ENOENT') {
      return [];
    }
    const err = new Error(`failed to load adapter registry at ${registryPath}: ${error.message}`);
    err.cause = error;
    throw err;
  }
}

async function emitAdapterSkeletons(mismatches, directory) {
  if (!directory) {
    return [];
  }
  const todo = (Array.isArray(mismatches) ? mismatches : []).filter((entry) => {
    return !entry.adapter && entry.actual && entry.expected;
  });
  if (todo.length === 0) {
    return [];
  }

  const targetDir = path.resolve(process.cwd(), directory);
  await fs.mkdir(targetDir, { recursive: true });
  const seen = new Set();
  const emitted = [];

  for (const mismatch of todo) {
    const from = normalizeDescriptor(mismatch.actual);
    const to = normalizeDescriptor(mismatch.expected);
    if (!from || !to) {
      continue;
    }
    const op = opNameForAdapter(from, to);
    if (seen.has(op)) {
      continue;
    }
    seen.add(op);

    const fileSlug = op.replace(/[^A-Za-z0-9]+/g, '_');
    const filePath = path.join(targetDir, `${fileSlug}.mjs`);
    const alreadyExists = await fileExists(filePath);
    if (!alreadyExists) {
      const importPath = relativeImportPath(path.dirname(filePath), TRANSFORM_MODULE_PATH);
      const fromLabel = formatTypeDescriptor(from);
      const toLabel = formatTypeDescriptor(to);
      const header = [
        '// @generated by tf typecheck --emit-adapters',
        `// Source: ${fromLabel}`,
        `// Target: ${toLabel}`,
      ];
      if (mismatch.nodeId) {
        header.push(`// Node: ${mismatch.nodeId}`);
      }
      if (mismatch.port) {
        header.push(`// Port: ${mismatch.port}`);
      }
      if (mismatch.sourceVar) {
        header.push(`// Source var: ${mismatch.sourceVar}`);
      }
      const stub = `${header.join('\n')}
import { registerTransform } from '${importPath}';

const OP = '${op}';

export function registerAdapter() {
  registerTransform(OP, (spec, input = {}) => {
    const value = input.value ?? input;
    throw new Error("TODO: implement deterministic adapter ${fromLabel} -> ${toLabel}");
  });
}

export default registerAdapter;
`;
      await fs.writeFile(filePath, `${stub.trim()}\n`, 'utf8');
    }
    emitted.push({ op, file: filePath, created: !alreadyExists });
  }

  return emitted;
}

function collectInputBindings(binding) {
  const results = [];
  const visit = (value, pathSegments) => {
    if (typeof value === 'string') {
      if (value.startsWith('@')) {
        const ref = value.slice(1);
        if (ref.length > 0) {
          const base = ref.split('.')[0];
          if (base) {
            results.push({ portPath: [...pathSegments], sourceVar: base });
          }
        }
      }
      return;
    }
    if (Array.isArray(value)) {
      value.forEach((entry, index) => {
        visit(entry, [...pathSegments, index]);
      });
      return;
    }
    if (value && typeof value === 'object') {
      for (const [key, nested] of Object.entries(value)) {
        visit(nested, [...pathSegments, key]);
      }
    }
  };
  visit(binding, []);
  return results;
}

function getMetadataPortTypes(node) {
  const metadata = node && typeof node === 'object' ? node.metadata : null;
  if (!metadata || typeof metadata !== 'object') {
    return null;
  }
  const portTypes = metadata.port_types ?? metadata.portTypes ?? null;
  if (!portTypes || typeof portTypes !== 'object') {
    return null;
  }
  return portTypes;
}

function getSection(portTypes, direction) {
  if (!portTypes || typeof portTypes !== 'object') {
    return null;
  }
  const keys = direction === 'in' ? ['in', 'inputs'] : ['out', 'outputs'];
  for (const key of keys) {
    const candidate = portTypes[key];
    if (candidate && typeof candidate === 'object') {
      return candidate;
    }
  }
  return null;
}

function extractDescriptor(candidate) {
  if (!candidate || typeof candidate !== 'object') {
    return null;
  }
  if (!Array.isArray(candidate)) {
    const normalized = normalizeDescriptor(candidate);
    if (normalized) {
      return normalized;
    }
  }
  if (candidate.type) {
    const normalized = normalizeDescriptor(candidate.type);
    if (normalized) {
      return normalized;
    }
  }
  if (candidate.default) {
    const normalized = normalizeDescriptor(candidate.default);
    if (normalized) {
      return normalized;
    }
  }
  if (candidate['*']) {
    const normalized = normalizeDescriptor(candidate['*']);
    if (normalized) {
      return normalized;
    }
  }
  return null;
}

function selectNext(candidate, segment) {
  if (!candidate || typeof candidate !== 'object') {
    return null;
  }
  const key = typeof segment === 'number' ? String(segment) : segment;
  if (key !== undefined && key !== null && Object.prototype.hasOwnProperty.call(candidate, key)) {
    return candidate[key];
  }
  if (typeof segment === 'number' && Object.prototype.hasOwnProperty.call(candidate, '*')) {
    return candidate['*'];
  }
  if (Object.prototype.hasOwnProperty.call(candidate, '*')) {
    return candidate['*'];
  }
  if (Object.prototype.hasOwnProperty.call(candidate, 'default')) {
    return candidate.default;
  }
  if (Object.prototype.hasOwnProperty.call(candidate, 'var')) {
    return candidate.var;
  }
  return null;
}

function resolveInputDescriptor(node, portPath) {
  const portTypes = getMetadataPortTypes(node);
  const section = getSection(portTypes, 'in');
  if (!section || typeof section !== 'object') {
    return null;
  }
  if (!Array.isArray(portPath) || portPath.length === 0) {
    return extractDescriptor(section);
  }
  let current = section;
  for (const segment of portPath) {
    current = selectNext(current, segment);
    if (!current || typeof current !== 'object') {
      return normalizeDescriptor(current);
    }
  }
  return extractDescriptor(current);
}

function getOutputDescriptors(node) {
  const descriptors = new Map();
  const portTypes = getMetadataPortTypes(node);
  const section = getSection(portTypes, 'out');
  if (section && typeof section === 'object') {
    for (const [port, descriptor] of Object.entries(section)) {
      const normalized = normalizeDescriptor(descriptor);
      if (normalized) {
        descriptors.set(port, normalized);
      }
    }
  }

  const binding = node?.out;
  if (binding && typeof binding === 'object' && !Array.isArray(binding)) {
    const varName = typeof binding.var === 'string' ? binding.var : null;
    if (varName) {
      let descriptor = normalizeDescriptor(binding.type);
      if (!descriptor && descriptors.has(varName)) {
        descriptor = descriptors.get(varName);
      }
      if (!descriptor && descriptors.has('default')) {
        descriptor = descriptors.get('default');
      }
      if (!descriptor && descriptors.has('var')) {
        descriptor = descriptors.get('var');
      }
      if (descriptor) {
        descriptors.set(varName, descriptor);
      }
    }
  }

  return descriptors;
}

function findAdapter(adapters, actual, expected) {
  for (const adapter of adapters) {
    if (descriptorsEqual(adapter.from, actual) && descriptorsEqual(adapter.to, expected)) {
      return adapter;
    }
  }
  return null;
}

function checkNodeInputs(node, varTypes, adapters, mismatches) {
  const bindings = collectInputBindings(node?.in ?? null);
  if (bindings.length === 0) {
    return;
  }

  for (const { portPath, sourceVar } of bindings) {
    const expected = resolveInputDescriptor(node, portPath);
    if (!expected) {
      continue;
    }
    const actual = varTypes.get(sourceVar);
    if (!actual) {
      continue;
    }
    if (descriptorsEqual(actual, expected)) {
      continue;
    }
    const adapter = findAdapter(adapters, actual, expected);
    mismatches.push({
      nodeId: node?.id ?? '<unknown>',
      port: formatPortPath(portPath),
      portPath: [...portPath],
      sourceVar,
      expected,
      actual,
      adapter: adapter
        ? { id: adapter.id, op: adapter.op, description: adapter.description }
        : null,
    });
  }
}

function recordNodeOutputs(node, varTypes) {
  const outputs = getOutputDescriptors(node);
  if (outputs.size === 0) {
    return;
  }
  for (const [varName, descriptor] of outputs.entries()) {
    if (typeof varName !== 'string' || !descriptor) {
      continue;
    }
    varTypes.set(varName, descriptor);
  }
}

export async function typecheck(l0, options = {}) {
  if (!l0 || typeof l0 !== 'object') {
    throw new Error('typecheck expected an L0 pipeline object');
  }
  const registryPath = options.registryPath
    ? path.resolve(options.registryPath)
    : DEFAULT_REGISTRY_PATH;
  const adapters = await loadAdapterRegistry(registryPath);
  const varTypes = new Map();
  const mismatches = [];

  const nodes = Array.isArray(l0.nodes) ? l0.nodes : [];
  for (const node of nodes) {
    checkNodeInputs(node, varTypes, adapters, mismatches);
    recordNodeOutputs(node, varTypes);
  }

  const suggestions = mismatches.filter((entry) => entry.adapter);
  let status = 'ok';
  if (mismatches.length > 0) {
    status = mismatches.every((entry) => entry.adapter) ? 'needs-adapter' : 'error';
  }

  let emittedAdapters = [];
  if (options.emitAdaptersDir) {
    emittedAdapters = await emitAdapterSkeletons(mismatches, options.emitAdaptersDir);
  }

  return {
    status,
    mismatches,
    suggestions,
    registryPath,
    checkedNodes: nodes.length,
    knownAdapters: adapters.map((entry) => ({ id: entry.id, op: entry.op })),
    describe: formatTypeDescriptor,
    emittedAdapters,
  };
}

export async function typecheckFile(filePath, options = {}) {
  const absolute = path.resolve(process.cwd(), filePath);
  const raw = await fs.readFile(absolute, 'utf8');
  const parsed = JSON.parse(raw);
  return typecheck(parsed, options);
}

export default typecheck;
