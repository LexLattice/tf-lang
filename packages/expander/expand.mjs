import { readFileSync } from 'node:fs';
import * as YAML from 'yaml';
import { annotateInstances } from './resolve.mjs';

const MACRO_PREFIXES = ['interaction.', 'transform.', 'policy.', 'obs.', 'state.', 'process.'];
const KERNEL_KINDS = new Set(['Transform', 'Publish', 'Subscribe', 'Keypair']);

function preprocessL2Yaml(source) {
  const lines = source.split(/\r?\n/);
  const result = [];
  let capturing = false;
  let depth = 0;
  for (const line of lines) {
    if (!capturing) {
      const match = line.match(/^(\s*[^:#]+:\s+)([^\s].*)$/);
      if (match) {
        const [, prefix, rest] = match;
        const trimmed = rest.trimStart();
        if (MACRO_PREFIXES.some((p) => trimmed.startsWith(p))) {
          capturing = true;
          depth = countParens(rest);
          let rewritten = prefix + "'" + rest;
          if (depth <= 0) {
            rewritten += "'";
            capturing = false;
          }
          result.push(rewritten);
          continue;
        }
      }
      result.push(line);
      continue;
    }
    depth += countParens(line);
    if (depth <= 0) {
      result.push(line + "'");
      capturing = false;
    } else {
      result.push(line);
    }
  }
  if (capturing) {
    throw new Error('Unbalanced macro invocation in L2 YAML');
  }
  return result.join('\n');
}

function countParens(str) {
  const opens = (str.match(/\(/g) || []).length;
  const closes = (str.match(/\)/g) || []).length;
  return opens - closes;
}

function parseCall(value) {
  if (typeof value !== 'string') {
    throw new Error(`Expected macro invocation string, got ${typeof value}`);
  }
  const match = value.trim().match(/^([a-zA-Z0-9_.]+)\((.*)\)$/s);
  if (!match) {
    throw new Error(`Unable to parse macro invocation: ${value}`);
  }
  const [, name, argsRaw] = match;
  const args = argsRaw.trim() ? YAML.parse(`{${argsRaw}}`) : {};
  return { name, args };
}

function combineWhen(parent, child) {
  if (parent && child) {
    return `(${parent}) && (${child})`;
  }
  return child || parent;
}

function refToVar(ref) {
  if (typeof ref !== 'string') return ref;
  return ref.startsWith('@') ? ref.slice(1) : ref;
}

function pushNode(ctx, node, when, domainOverride) {
  if (!KERNEL_KINDS.has(node.kind)) {
    throw new Error(`Non-kernel node emitted: ${node.kind}`);
  }
  const final = { ...node };
  const gating = combineWhen(when, node.when);
  if (gating) {
    final.when = gating;
  }
  ctx.nodes.push(final);
  const domain = domainOverride ?? ctx.domainStack[ctx.domainStack.length - 1];
  if (domain) {
    ctx.nodeDomains.set(final, domain);
  }
}

function expandInteractionReceive(ctx, alias, args, when) {
  const node = {
    id: `S_${alias}`,
    kind: 'Subscribe',
    channel: `rpc:req:${args.endpoint}`,
    qos: args.qos || 'at_least_once',
    out: { var: alias },
  };
  pushNode(ctx, node, when);
}

function expandTransformValidate(ctx, alias, args, when) {
  const node = {
    id: `T_${alias}`,
    kind: 'Transform',
    spec: {
      op: 'jsonschema.validate',
      schema: args.schema,
    },
    in: {
      value: args.input,
    },
    out: { var: alias },
  };
  pushNode(ctx, node, when);
}

function expandTransformModelInfer(ctx, alias, args, when) {
  const node = {
    id: `T_${alias}`,
    kind: 'Transform',
    spec: {
      op: 'model_infer',
      model: args.model,
    },
    in: {
      features: args.input,
    },
    out: { var: alias },
  };
  pushNode(ctx, node, when);
}

function expandPolicyEvaluate(ctx, alias, args, when) {
  const node = {
    id: `T_${alias}`,
    kind: 'Transform',
    spec: {
      op: 'policy_eval',
      policy: args.policy,
    },
    in: {
      input: args.input,
    },
    out: { var: alias },
  };
  pushNode(ctx, node, when);
}

function buildCanonicalRequestObject(identityVar, args, method) {
  const canonical = {
    k: `@${identityVar}.public_key_pem`,
    e: args.endpoint,
    m: method,
  };
  if (args.query) {
    canonical.query = args.query;
  }
  if (args.body) {
    canonical.body = args.body;
  }
  return canonical;
}

function expandInteractionRequest(ctx, alias, args, when) {
  const method = args.method || (args.body ? 'POST' : 'GET');
  const identityVar = `${alias}_identity`;
  const corrVar = `${alias}_corr`;
  const replyVar = `${alias}_reply_to`;

  pushNode(ctx, {
    id: `K_${alias}_identity`,
    kind: 'Keypair',
    algorithm: 'Ed25519',
    out: { var: identityVar },
  }, when);

  pushNode(ctx, {
    id: `T_${alias}_corr`,
    kind: 'Transform',
    spec: { op: 'hash', alg: 'blake3' },
    in: buildCanonicalRequestObject(identityVar, args, method),
    out: { var: corrVar },
  }, when);

  pushNode(ctx, {
    id: `T_${alias}_reply_to`,
    kind: 'Transform',
    spec: { op: 'concat' },
    in: ['rpc:reply:', `@${corrVar}`],
    out: { var: replyVar },
  }, when);

  const payload = {
    method,
    corr: `@${corrVar}`,
    reply_to: `@${replyVar}`,
  };
  if (args.headers) {
    payload.headers = args.headers;
  }
  if (args.query) {
    payload.query = args.query;
  }
  if (args.body) {
    payload.body = args.body;
  }

  pushNode(ctx, {
    id: `P_${alias}`,
    kind: 'Publish',
    channel: `rpc:req:${args.endpoint}`,
    qos: args.qos || 'at_least_once',
    payload,
  }, when);

  pushNode(ctx, {
    id: `S_${alias}`,
    kind: 'Subscribe',
    channel: `@${replyVar}`,
    qos: args.response_qos || 'at_least_once',
    filter: `@${corrVar}`,
    out: { var: alias },
  }, when);
}

function expandInteractionReply(ctx, alias, args, when) {
  const target = refToVar(args.to);
  const payload = {
    corr: `@${target}.corr`,
    status: args.status || 'ok',
  };
  if (args.body) {
    payload.body = args.body;
  }
  pushNode(ctx, {
    id: `P_${alias}`,
    kind: 'Publish',
    channel: `@${target}.reply_to`,
    qos: args.qos || 'at_least_once',
    payload,
  }, when);
}

function expandObsEmitMetric(ctx, alias, args, when) {
  pushNode(ctx, {
    id: `P_${alias}`,
    kind: 'Publish',
    channel: `metric:${args.name}`,
    qos: args.qos || 'at_least_once',
    payload: {
      value: args.value ?? 1,
      unit: args.unit || 'count',
      tags: args.tags || {},
    },
  }, when);
}

function expandPolicyRecordDecision(ctx, alias, args, when) {
  const digestVar = `${alias}_digest`;
  const idVar = `${alias}_id`;
  const ts = ctx.createdAt;
  pushNode(ctx, {
    id: `T_${alias}_digest`,
    kind: 'Transform',
    spec: { op: 'digest', alg: 'blake3' },
    in: { kind: args.kind, payload: args.payload, ts },
    out: { var: digestVar },
  }, when);
  pushNode(ctx, {
    id: `T_${alias}_id`,
    kind: 'Transform',
    spec: { op: 'encode_base58' },
    in: { value: `@${digestVar}` },
    out: { var: idVar },
  }, when);
  pushNode(ctx, {
    id: `P_${alias}`,
    kind: 'Publish',
    channel: 'policy:record',
    qos: args.qos || 'at_least_once',
    payload: {
      record_id: `@${idVar}`,
      kind: args.kind,
      payload: args.payload,
      ts,
    },
  }, when);
}

function expandStateDiff(ctx, alias, args, when) {
  pushNode(ctx, {
    id: `T_${alias}`,
    kind: 'Transform',
    spec: { op: 'state_diff' },
    in: { base: args.base, target: args.target },
    out: { var: alias },
  }, when);
}

function expandProcessSchedule(ctx, alias, args, when) {
  const method = 'POST';
  const endpoint = 'scheduler.request';
  const identityVar = `${alias}_identity`;
  const corrVar = `${alias}_corr`;
  const replyVar = `${alias}_reply_to`;
  const body = {};
  if ('task_ref' in args) {
    body.task_ref = args.task_ref;
  }
  if ('trigger' in args) {
    body.trigger = args.trigger;
  }

  pushNode(ctx, {
    id: `K_${alias}_identity`,
    kind: 'Keypair',
    algorithm: 'Ed25519',
    out: { var: identityVar },
  }, when);

  pushNode(ctx, {
    id: `T_${alias}_corr`,
    kind: 'Transform',
    spec: { op: 'hash', alg: 'blake3' },
    in: buildCanonicalRequestObject(identityVar, { endpoint, body }, method),
    out: { var: corrVar },
  }, when);

  pushNode(ctx, {
    id: `T_${alias}_reply_to`,
    kind: 'Transform',
    spec: { op: 'concat' },
    in: ['rpc:reply:', `@${corrVar}`],
    out: { var: replyVar },
  }, when);

  pushNode(ctx, {
    id: `P_${alias}`,
    kind: 'Publish',
    channel: `rpc:req:${endpoint}`,
    qos: args.qos || 'at_least_once',
    payload: {
      method,
      body,
      corr: `@${corrVar}`,
      reply_to: `@${replyVar}`,
    },
  }, when);

  pushNode(ctx, {
    id: `S_${alias}`,
    kind: 'Subscribe',
    channel: `@${replyVar}`,
    qos: args.response_qos || 'at_least_once',
    filter: `@${corrVar}`,
    out: { var: alias },
  }, when);
}

const MACROS = {
  'interaction.receive': expandInteractionReceive,
  'transform.validate': expandTransformValidate,
  'transform.model_infer': expandTransformModelInfer,
  'policy.evaluate': expandPolicyEvaluate,
  'interaction.request': expandInteractionRequest,
  'interaction.reply': expandInteractionReply,
  'obs.emit_metric': expandObsEmitMetric,
  'policy.record_decision': expandPolicyRecordDecision,
  'state.diff': expandStateDiff,
  'process.schedule': expandProcessSchedule,
};

function expandCall(ctx, alias, value, when) {
  const { name, args } = parseCall(value);
  const handler = MACROS[name];
  if (!handler) {
    throw new Error(`Unsupported macro: ${name}`);
  }
  const domain = name.includes('.') ? name.split('.')[0] : undefined;
  ctx.domainStack.push(domain);
  try {
    handler(ctx, alias, args, when);
  } finally {
    ctx.domainStack.pop();
  }
}

function expandSteps(ctx, steps, when) {
  if (!Array.isArray(steps)) return;
  for (const entry of steps) {
    const [[alias, value]] = Object.entries(entry);
    if (alias === 'branch') {
      const branch = value;
      const condition = branch.when;
      expandSteps(ctx, branch.then || [], combineWhen(when, condition));
      if (branch.else) {
        const negated = `!(${condition})`;
        expandSteps(ctx, branch.else, combineWhen(when, negated));
      }
      continue;
    }
    expandCall(ctx, alias, value, when);
  }
}

function computeEffects(nodes) {
  const order = ['Outbound', 'Inbound', 'Entropy', 'Pure'];
  const effectMap = {
    Publish: 'Outbound',
    Subscribe: 'Inbound',
    Keypair: 'Entropy',
    Transform: 'Pure',
  };
  const seen = new Set();
  for (const node of nodes) {
    const effect = effectMap[node.kind];
    if (effect) {
      seen.add(effect);
    }
  }
  return order.filter((name) => seen.has(name)).join('+');
}

export function expandL2ObjectToL0(doc, options = {}) {
  const createdAt = options.createdAt || new Date().toISOString();
  const ctx = {
    createdAt,
    nodes: [],
    domainStack: [undefined],
    nodeDomains: new WeakMap(),
  };

  expandSteps(ctx, doc.inputs || [], undefined);
  expandSteps(ctx, doc.steps || [], undefined);
  expandSteps(ctx, doc.outputs || [], undefined);

  const nodes = annotateInstances({
    nodes: ctx.nodes,
    domainOf: (node) => ctx.nodeDomains.get(node),
  });
  const effects = computeEffects(nodes);

  return {
    pipeline_id: doc.pipeline,
    created_at: createdAt,
    effects,
    nodes,
  };
}

export function expandPipelineFromYaml(yamlSource, options = {}) {
  const prepared = preprocessL2Yaml(yamlSource);
  const l2 = YAML.parse(prepared);
  return expandL2ObjectToL0(l2, options);
}

export function expandPipelineFromFile(filePath, options = {}) {
  const yamlSource = readFileSync(filePath, 'utf-8');
  return expandPipelineFromYaml(yamlSource, options);
}

export { expandL2ObjectToL0 as expandPipeline };
export default expandL2ObjectToL0;
