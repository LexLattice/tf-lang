import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { DETERMINISTIC_TRANSFORMS } from '../runtime/run.mjs';
import { checkIdempotency } from '../../laws/idempotency.mjs';
import checkSampleCrdtMerge from '../../laws/crdt-merge.mjs';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const EFFECT_ORDER = ['Outbound', 'Inbound', 'Entropy', 'Pure'];
const CAPABILITY_LATTICE_DEFAULT = path.resolve(__dirname, '../../policy/capability.lattice.json');

function collectVarRefs(value) {
  const refs = new Set();
  const visit = (input) => {
    if (typeof input === 'string' && input.startsWith('@')) {
      const ref = input.slice(1);
      if (ref.length > 0) {
        refs.add(ref.split('.')[0]);
      }
      return;
    }
    if (Array.isArray(input)) {
      for (const item of input) {
        visit(item);
      }
      return;
    }
    if (input && typeof input === 'object') {
      for (const value of Object.values(input)) {
        visit(value);
      }
    }
  };
  visit(value);
  return Array.from(refs);
}

function dependsOnKeypair(varName, varMeta, seen = new Set()) {
  if (!varName || seen.has(varName)) {
    return false;
  }
  seen.add(varName);
  const meta = varMeta.get(varName);
  if (!meta) {
    return false;
  }
  if (meta.kind === 'Keypair') {
    return true;
  }
  if (!Array.isArray(meta.deps) || meta.deps.length === 0) {
    return false;
  }
  return meta.deps.some((dep) => dependsOnKeypair(dep, varMeta, seen));
}

function computeRpcPairing({ publishNodes = [], subsByChannelVar = new Map() }) {
  const results = [];

  for (const meta of publishNodes) {
    const channel = typeof meta.node.channel === 'string' ? meta.node.channel : '';
    if (!channel.startsWith('rpc:req:')) {
      continue;
    }
    const replyRefs = Array.isArray(meta.replyRefs) ? meta.replyRefs : [];
    const corrRefs = Array.isArray(meta.corrRefs) ? meta.corrRefs : [];
    let hasReplySub = false;
    let filterMatchesCorr = false;

    for (const replyVar of replyRefs) {
      const subscribers = subsByChannelVar.get(replyVar) ?? [];
      if (subscribers.length > 0) {
        hasReplySub = true;
        if (!filterMatchesCorr) {
          filterMatchesCorr = subscribers.some(({ filterRefs }) => {
            if (!Array.isArray(filterRefs) || filterRefs.length !== 1) {
              return false;
            }
            const [ref] = filterRefs;
            return corrRefs.includes(ref);
          });
        }
      }
    }

    const ok = hasReplySub && filterMatchesCorr;
    results.push({
      id: meta.node.id,
      hasReplySub,
      filterMatchesCorr,
      ok,
    });
  }

  return {
    ok: results.every((entry) => entry.ok),
    results,
  };
}

function normalizeEffects(effects) {
  if (!effects) {
    return [];
  }
  return String(effects)
    .split('+')
    .map((item) => item.trim())
    .filter(Boolean);
}

function formatEffects(effectsPresent) {
  const ordered = EFFECT_ORDER.filter((effect) => effectsPresent.has(effect));
  if (ordered.length === 0) {
    return 'Pure';
  }
  return ordered.join('+');
}

function loadPolicy(policyPath) {
  return fs.readFile(policyPath, 'utf8')
    .then((content) => JSON.parse(content))
    .catch((error) => {
      const err = new Error(`failed to load policy allow list: ${error.message}`);
      err.cause = error;
      throw err;
    });
}

function compilePolicy(patterns = []) {
  return patterns.map((pattern) => {
    const escaped = pattern.replace(/[.*+?^${}()|[\]\\]/g, '\\$&').replace(/\\\*/g, '.*');
    return { raw: pattern, regex: new RegExp(`^${escaped}$`) };
  });
}

function matchesPolicy(channel, compiled) {
  return compiled.some((entry) => entry.regex.test(channel));
}

function compileCapabilityPatterns(entries = []) {
  return entries
    .map((entry) => {
      if (!entry || typeof entry.pattern !== 'string' || typeof entry.capability !== 'string') {
        return null;
      }
      const escaped = entry.pattern
        .replace(/[.*+?^${}()|[\]\\]/g, '\\$&')
        .replace(/\\\*/g, '.*');
      return { capability: entry.capability, regex: new RegExp(`^${escaped}$`) };
    })
    .filter(Boolean);
}

function compileCapabilityLattice(lattice = {}) {
  const publish = compileCapabilityPatterns(Array.isArray(lattice.publish) ? lattice.publish : []);
  const subscribe = compileCapabilityPatterns(Array.isArray(lattice.subscribe) ? lattice.subscribe : []);
  const keypairEntries = lattice.keypair && typeof lattice.keypair === 'object'
    ? Object.entries(lattice.keypair)
    : [];
  const keypair = new Map(
    keypairEntries
      .filter(([, capability]) => typeof capability === 'string')
      .map(([algorithm, capability]) => [algorithm, capability])
  );
  return { publish, subscribe, keypair };
}

function matchChannelCapability(channel, compiled, fallbackPrefix) {
  if (typeof channel !== 'string' || channel.length === 0 || channel.startsWith('@')) {
    return null;
  }
  for (const entry of compiled) {
    if (entry.regex.test(channel)) {
      return entry.capability;
    }
  }
  return fallbackPrefix ? `${fallbackPrefix}:${channel}` : null;
}

function resolveKeypairCapability(algorithm, keypairMap) {
  if (typeof algorithm !== 'string' || algorithm.length === 0) {
    return null;
  }
  if (keypairMap instanceof Map) {
    const direct = keypairMap.get(algorithm);
    if (typeof direct === 'string' && direct.length > 0) {
      return direct;
    }
    const fallback = keypairMap.get('*');
    if (typeof fallback === 'string' && fallback.length > 0) {
      return fallback;
    }
  }
  return `cap:keypair:${algorithm}`;
}

async function loadCapabilityLattice(latticePath = CAPABILITY_LATTICE_DEFAULT) {
  try {
    const raw = await fs.readFile(latticePath, 'utf8');
    return JSON.parse(raw);
  } catch (error) {
    if (error?.code === 'ENOENT') {
      return {};
    }
    const err = new Error(`failed to load capability lattice: ${error.message}`);
    err.cause = error;
    throw err;
  }
}

function analyzePipeline(l0, capabilityLattice = { publish: [], subscribe: [], keypair: new Map() }) {
  const varMeta = new Map();
  const effectsPresent = new Set();
  const publishNodes = [];
  const subscriptions = [];
  const subscriptionDetails = new Map();
  const capabilities = new Set();
  const publishCaps = Array.isArray(capabilityLattice.publish) ? capabilityLattice.publish : [];
  const subscribeCaps = Array.isArray(capabilityLattice.subscribe) ? capabilityLattice.subscribe : [];
  const keypairCaps = capabilityLattice.keypair instanceof Map
    ? capabilityLattice.keypair
    : new Map();

  for (const node of l0.nodes ?? []) {
    switch (node.kind) {
      case 'Transform': {
        effectsPresent.add('Pure');
        const outVar = node.out?.var;
        if (outVar) {
          const refs = collectVarRefs(node.in);
          const depsStable = refs.every((ref) => (varMeta.get(ref)?.stable ?? false));
          const deterministic = DETERMINISTIC_TRANSFORMS.has(node.spec?.op);
          const stable = deterministic && depsStable;
          varMeta.set(outVar, {
            id: node.id,
            kind: node.kind,
            op: node.spec?.op,
            stable,
            deterministic,
            deps: refs,
          });
        }
        break;
      }
      case 'Subscribe': {
        effectsPresent.add('Inbound');
        const outVar = node.out?.var;
        if (outVar) {
          varMeta.set(outVar, {
            id: node.id,
            kind: node.kind,
            stable: true,
            deterministic: false,
            deps: [],
          });
        }
        const filterRefs = collectVarRefs(node.filter);
        let channelVar = null;
        if (typeof node.channel === 'string' && node.channel.startsWith('@')) {
          const candidate = node.channel.slice(1);
          if (candidate && node.channel === `@${candidate}` && !candidate.includes('.')) {
            channelVar = candidate;
          }
        }
        const staticChannel = typeof node.channel === 'string' && !node.channel.startsWith('@')
          ? node.channel
          : null;
        if (staticChannel) {
          const cap = matchChannelCapability(staticChannel, subscribeCaps, 'cap:subscribe');
          if (cap) {
            capabilities.add(cap);
          }
        }
        subscriptions.push(node);
        subscriptionDetails.set(node, { filterRefs, channelVar });
        break;
      }
      case 'Publish': {
        effectsPresent.add('Outbound');
        const channelValue = node.channel;
        const dynamicChannel = typeof channelValue === 'string' && channelValue.startsWith('@');
        if (!dynamicChannel && typeof channelValue === 'string') {
          const cap = matchChannelCapability(channelValue, publishCaps, 'cap:publish');
          if (cap) {
            capabilities.add(cap);
          }
        }
        const corrValue = node.payload?.corr;
        const hasCorrField = Object.prototype.hasOwnProperty.call(node.payload ?? {}, 'corr');
        const corrRefs = hasCorrField ? collectVarRefs(corrValue) : [];
        const replyRefs = collectVarRefs(node.payload?.reply_to);
        const corrStable = hasCorrField
          ? (corrRefs.length === 0
            ? true
            : corrRefs.every((ref) => {
              const meta = varMeta.get(ref);
              return Boolean(meta?.stable) && meta?.kind === 'Transform';
            }))
          : false;
        publishNodes.push({
          node,
          dynamicChannel,
          corrRefs,
          hasCorr: hasCorrField,
          corrStable,
          replyRefs,
        });
        break;
      }
      case 'Keypair': {
        effectsPresent.add('Entropy');
        const outVar = node.out?.var;
        if (outVar) {
          varMeta.set(outVar, {
            id: node.id,
            kind: node.kind,
            stable: true,
            deterministic: false,
            deps: [],
          });
        }
        const algorithm = typeof node.algorithm === 'string' && node.algorithm.length > 0
          ? node.algorithm
          : 'keypair';
        const cap = resolveKeypairCapability(algorithm, keypairCaps);
        if (cap) {
          capabilities.add(cap);
        }
        break;
      }
      default:
        throw new Error(`unsupported node kind: ${node.kind}`);
    }
  }

  const subsByChannelVar = new Map();
  for (const sub of subscriptions) {
    const details = subscriptionDetails.get(sub);
    if (!details?.channelVar) {
      continue;
    }
    if (!subsByChannelVar.has(details.channelVar)) {
      subsByChannelVar.set(details.channelVar, []);
    }
    subsByChannelVar.get(details.channelVar).push({
      node: sub,
      filterRefs: details.filterRefs ?? [],
    });
  }

  for (const meta of publishNodes) {
    const channel = typeof meta.node.channel === 'string' ? meta.node.channel : '';
    if (channel.startsWith('rpc:req:')) {
      meta.entropyRooted = (meta.corrRefs ?? []).some((ref) => dependsOnKeypair(ref, varMeta));
    } else {
      meta.entropyRooted = false;
    }
  }

  return {
    varMeta,
    effectsPresent,
    publishNodes,
    subscriptions,
    subsByChannelVar,
    capabilities,
  };
}

function resolvePolicyPath(policyPath) {
  return policyPath
    ? path.resolve(policyPath)
    : path.resolve(__dirname, '../../policy/policy.allow.json');
}

async function loadCapabilities(capsPath) {
  if (!capsPath) {
    return [];
  }
  try {
    const content = await fs.readFile(capsPath, 'utf8');
    const parsed = JSON.parse(content);
    if (Array.isArray(parsed)) {
      return parsed.map((value) => String(value));
    }
    if (parsed && Array.isArray(parsed.capabilities)) {
      return parsed.capabilities.map((value) => String(value));
    }
    return [];
  } catch (error) {
    if (error?.code === 'ENOENT') {
      return [];
    }
    const err = new Error(`failed to load capabilities allow list: ${error.message}`);
    err.cause = error;
    throw err;
  }
}

function compileProvidedCapabilities(entries = []) {
  const exact = new Set();
  const matchers = [];
  for (const entry of entries) {
    if (typeof entry !== 'string') {
      continue;
    }
    if (entry.includes('*')) {
      const escaped = entry
        .replace(/[.*+?^${}()|[\]\\]/g, '\\$&')
        .replace(/\\\*/g, '.*');
      matchers.push(new RegExp(`^${escaped}$`));
      continue;
    }
    exact.add(entry);
  }
  return { exact, matchers };
}

function capabilitySatisfied(required, compiled) {
  if (!required) {
    return true;
  }
  if (compiled.exact.has(required)) {
    return true;
  }
  return compiled.matchers.some((regex) => regex.test(required));
}

async function runChecks(l0, options = {}) {
  const policyPath = resolvePolicyPath(options.policyPath);
  const capsPath = options.capsPath
    ? path.resolve(options.capsPath)
    : policyPath;
  const capabilityLattice = compileCapabilityLattice(await loadCapabilityLattice());
  const analysis = analyzePipeline(l0, capabilityLattice);

  const declaredEffects = normalizeEffects(l0.effects);
  const computedEffects = formatEffects(analysis.effectsPresent);
  const computedList = computedEffects.split('+');
  const missing = computedList.filter((effect) => !declaredEffects.includes(effect));
  const missingCritical = missing.filter((effect) => effect !== 'Pure' && effect !== 'Entropy');
  const extra = declaredEffects.filter((effect) => !computedList.includes(effect));
  const effects = {
    declared: declaredEffects.join('+') || null,
    computed: computedEffects,
    missing,
    extra,
    ok: missingCritical.length === 0 && extra.length === 0,
  };

  const policyAllow = await loadPolicy(policyPath);
  const publishPolicy = compilePolicy(policyAllow.publish ?? []);
  const subscribePolicy = compilePolicy(policyAllow.subscribe ?? []);

  const policy = {
    publish: { violations: [], dynamic: [] },
    subscribe: { violations: [], dynamic: [] },
  };

  for (const node of l0.nodes ?? []) {
    if (node.kind === 'Publish') {
      const channel = node.channel;
      if (typeof channel === 'string' && channel.startsWith('@')) {
        policy.publish.dynamic.push({ id: node.id, kind: node.kind, channel });
      } else if (typeof channel === 'string') {
        if (!matchesPolicy(channel, publishPolicy)) {
          policy.publish.violations.push({ id: node.id, kind: node.kind, channel });
        }
      }
    } else if (node.kind === 'Subscribe') {
      const channel = node.channel;
      if (typeof channel === 'string' && channel.startsWith('@')) {
        policy.subscribe.dynamic.push({ id: node.id, kind: node.kind, channel });
      } else if (typeof channel === 'string') {
        if (!matchesPolicy(channel, subscribePolicy)) {
          policy.subscribe.violations.push({ id: node.id, kind: node.kind, channel });
        }
      }
    }
  }

  policy.publish.ok = policy.publish.violations.length === 0;
  policy.subscribe.ok = policy.subscribe.violations.length === 0;

  const requiredCapabilities = Array.from(analysis.capabilities).sort();
  const providedList = await loadCapabilities(capsPath);
  const compiledProvided = compileProvidedCapabilities(providedList);
  const missingCapabilities = requiredCapabilities
    .filter((cap) => !capabilitySatisfied(cap, compiledProvided));
  const capabilities = {
    required: requiredCapabilities,
    missing: missingCapabilities,
    ok: missingCapabilities.length === 0,
  };

  const laws = {
    idempotency: { ok: true, results: [] },
    crdt_merge: { ok: true, results: [] },
    rpc_pairing: { ok: true, results: [] },
  };

  try {
    laws.rpc_pairing = computeRpcPairing({
      publishNodes: analysis.publishNodes,
      subsByChannelVar: analysis.subsByChannelVar,
    });
  } catch (error) {
    laws.rpc_pairing = {
      ok: false,
      results: [],
      error: error.message,
    };
  }

  try {
    laws.idempotency = await checkIdempotency({ publishNodes: analysis.publishNodes });
  } catch (error) {
    laws.idempotency = {
      ok: false,
      results: [],
      error: error.message,
    };
  }

  try {
    laws.crdt_merge = checkSampleCrdtMerge();
  } catch (error) {
    laws.crdt_merge = {
      ok: false,
      results: [],
      error: error.message,
    };
  }

  const overallGreen = effects.ok
    && policy.publish.ok
    && policy.subscribe.ok
    && capabilities.ok
    && laws.rpc_pairing.ok
    && laws.idempotency.ok
    && laws.crdt_merge.ok;

  return {
    pipeline_id: l0.pipeline_id ?? 'unknown',
    status: overallGreen ? 'GREEN' : 'RED',
    timestamp: new Date().toISOString(),
    effects,
    policy,
    capabilities,
    laws,
  };
}

export async function checkL0(filePath, options = {}) {
  const policyPath = resolvePolicyPath(options.policyPath);
  const capsPath = options.capsPath
    ? path.resolve(options.capsPath)
    : policyPath;
  const absolutePath = path.resolve(process.cwd(), filePath);
  const content = await fs.readFile(absolutePath, 'utf8');
  const l0 = JSON.parse(content);
  return runChecks(l0, { policyPath, capsPath });
}

function parseArgs(argv) {
  const args = argv.slice(2);
  if (args.length === 0) {
    throw new Error('usage: node packages/checker/check.mjs <pipeline.l0.json> [--policy path] [--caps path] [--out path]');
  }
  const file = args[0];
  let policyPath = path.resolve(__dirname, '../../policy/policy.allow.json');
  let outPath = path.resolve(__dirname, '../../out/TFREPORT.json');
  let capsPath = policyPath;

  for (let i = 1; i < args.length; i += 1) {
    const arg = args[i];
    if (arg === '--policy') {
      policyPath = path.resolve(process.cwd(), args[i + 1]);
      i += 1;
    } else if (arg === '--caps') {
      capsPath = path.resolve(process.cwd(), args[i + 1]);
      i += 1;
    } else if (arg === '--out') {
      outPath = path.resolve(process.cwd(), args[i + 1]);
      i += 1;
    }
  }

  return { file: path.resolve(process.cwd(), file), policyPath, capsPath, outPath };
}

async function main() {
  let exitCode = 0;
  let outPath = path.resolve(__dirname, '../../out/TFREPORT.json');
  try {
    const args = parseArgs(process.argv);
    outPath = args.outPath;
    const content = await fs.readFile(args.file, 'utf8');
    const l0 = JSON.parse(content);
    const report = await runChecks(l0, args);
    await fs.mkdir(path.dirname(args.outPath), { recursive: true });
    await fs.writeFile(args.outPath, `${JSON.stringify(report, null, 2)}\n`);
    if (report.status !== 'GREEN') {
      exitCode = 1;
    }
  } catch (error) {
    const fallback = {
      pipeline_id: null,
      status: 'RED',
      timestamp: new Date().toISOString(),
      error: error.message,
    };
    await fs.mkdir(path.dirname(outPath), { recursive: true });
    await fs.writeFile(outPath, `${JSON.stringify(fallback, null, 2)}\n`);
    console.error(error.message);
    exitCode = 1;
  }
  process.exit(exitCode);
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main();
}

export default runChecks;
