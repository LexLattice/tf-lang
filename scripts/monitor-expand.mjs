#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { parse as parseYaml } from 'yaml';
import {
  quoteCalls,
  parseCall,
  slug,
  nodeId,
  computeEffects,
} from '../packages/expander/common.mjs';

function prefixedId(prefix, name) {
  return `${prefix}_${slug(name)}`;
}

function usage() {
  console.error('usage: monitor-expand <input.l2.yaml> <output.l0.json>');
  process.exit(2);
}

const ALLOWED_KINDS = new Set(['Transform', 'Publish', 'Subscribe', 'Keypair']);

class MonitorCompiler {
  constructor(definition, outputPath) {
    this.definition = definition;
    this.outputPath = outputPath;
    this.bundleId = path.basename(outputPath, '.l0.json');
    this.createdAt = this.readExistingCreatedAt();
    this.conditionIndex = 0;
    this.branchIndex = 0;
  }

  readExistingCreatedAt() {
    if (!fs.existsSync(this.outputPath)) return new Date().toISOString();
    try {
      const parsed = JSON.parse(fs.readFileSync(this.outputPath, 'utf8'));
      return parsed.created_at ?? new Date().toISOString();
    } catch {
      return new Date().toISOString();
    }
  }

  resolveRef(ref, refs) {
    if (typeof ref !== 'string' || !ref.startsWith('@')) return ref;
    const pathExpr = ref.slice(1);
    const [head, ...rest] = pathExpr.split('.');
    const mapped = refs.get(head) ?? `@${head}`;
    if (rest.length === 0) return mapped;
    const suffix = rest.join('.');
    return mapped.startsWith('@') ? `${mapped}.${suffix}` : `@${mapped}.${suffix}`;
  }

  resolveValue(value, refs) {
    if (Array.isArray(value)) return value.map((v) => this.resolveValue(v, refs));
    if (value && typeof value === 'object') {
      const out = {};
      for (const [k, v] of Object.entries(value)) out[k] = this.resolveValue(v, refs);
      return out;
    }
    if (typeof value === 'string') return this.resolveRef(value, refs);
    return value;
  }

  addNode(nodes, node, whenClause) {
    if (!ALLOWED_KINDS.has(node.kind)) {
      throw new Error(`invalid kernel kind: ${node.kind}`);
    }
    const finalNode = { ...node };
    if (whenClause) finalNode.when = whenClause;
    nodes.push(finalNode);
  }

  compileCondition(condition, refs, nodes, label, whenClause) {
    if (typeof condition !== 'string') throw new Error(`unsupported condition: ${JSON.stringify(condition)}`);
    const eqMatch = condition.match(/^@([A-Za-z0-9_.]+)\s*==\s*'([^']+)'$/);
    const condVar = `${slug(label)}_${++this.conditionIndex}_value`;
    if (eqMatch) {
      const leftExpr = this.resolveRef(`@${eqMatch[1]}`, refs);
      const rightValue = eqMatch[2];
      this.addNode(nodes, {
        id: nodeId(`T_${slug(label)}_cond`, this.conditionIndex),
        kind: 'Transform',
        spec: { op: 'eq' },
        in: { left: leftExpr, right: rightValue },
        out: { var: condVar },
      }, whenClause);
    } else {
      const valueExpr = this.resolveRef(condition, refs);
      this.addNode(nodes, {
        id: nodeId(`T_${slug(label)}_cond`, this.conditionIndex),
        kind: 'Transform',
        spec: { op: 'identity' },
        in: { value: valueExpr },
        out: { var: condVar },
      }, whenClause);
    }
    return {
      thenWhen: `@${condVar}`,
      elseWhen: { op: 'not', var: condVar },
      condVar,
    };
  }

  expandProcessSchedule(name, call, refs, nodes, whenClause) {
    const taskRef = call.args.task_ref;
    const trigger = this.resolveValue(call.args.trigger ?? {}, refs);
    const kpVar = `kp_${slug(name)}`;
    this.addNode(nodes, {
      id: prefixedId('K', name),
      kind: 'Keypair',
      algorithm: 'Ed25519',
      out: { var: kpVar },
    }, whenClause);
    const corrVar = `corr_${slug(name)}`;
    this.addNode(nodes, {
      id: `${prefixedId('T', name)}_corr`,
      kind: 'Transform',
      spec: { op: 'hash', alg: 'blake3' },
      in: { k: `@${kpVar}.public_key_pem`, task_ref: taskRef, trigger },
      out: { var: corrVar },
    }, whenClause);
    const replyToVar = `reply_to_${slug(name)}`;
    this.addNode(nodes, {
      id: `${prefixedId('T', name)}_reply_to`,
      kind: 'Transform',
      spec: { op: 'concat' },
      in: { a: 'rpc:reply:', b: `@${corrVar}` },
      out: { var: replyToVar },
    }, whenClause);
    this.addNode(nodes, {
      id: prefixedId('P', `${name}_request`),
      kind: 'Publish',
      channel: 'rpc:req:scheduler.request',
      qos: 'at_least_once',
      payload: {
        method: 'POST',
        body: { task_ref: taskRef, trigger },
        corr: `@${corrVar}`,
        reply_to: `@${replyToVar}`,
      },
    }, whenClause);
    const replyMsgVar = `${slug(name)}_reply`;
    this.addNode(nodes, {
      id: prefixedId('S', `${name}_reply`),
      kind: 'Subscribe',
      channel: `@${replyToVar}`,
      qos: 'at_least_once',
      filter: `@${corrVar}`,
      out: { var: replyMsgVar },
    }, whenClause);
    refs.set(name, `@${replyMsgVar}`);
  }

  expandTransformLookup(name, call, refs, nodes, whenClause) {
    const entity = call.args.entity;
    const field = call.args.field;
    const keyValue = this.resolveValue(call.args.key, refs);
    const outVar = `${slug(name)}_value`;
    this.addNode(nodes, {
      id: prefixedId('T', name),
      kind: 'Transform',
      spec: { op: 'lookup', entity, field },
      in: { key: keyValue },
      out: { var: outVar },
    }, whenClause);
    refs.set(name, `@${outVar}`);
  }

  expandEmitMetric(name, call, refs, nodes, whenClause) {
    const metricName = call.args.name;
    const value = this.resolveValue(call.args.value ?? 1, refs);
    const tags = this.resolveValue(call.args.tags ?? {}, refs);
    this.addNode(nodes, {
      id: prefixedId('P', name),
      kind: 'Publish',
      channel: `metric:${metricName}`,
      qos: 'at_least_once',
      payload: { value, unit: 'count', tags },
    }, whenClause);
  }

  expandInteractionRequest(name, call, refs, nodes, whenClause) {
    const endpoint = call.args.endpoint;
    const method = call.args.method ?? 'POST';
    const body = call.args.body ? this.resolveValue(call.args.body, refs) : undefined;
    const query = call.args.query ? this.resolveValue(call.args.query, refs) : undefined;
    const kpVar = `kp_${slug(name)}`;
    this.addNode(nodes, {
      id: prefixedId('K', name),
      kind: 'Keypair',
      algorithm: 'Ed25519',
      out: { var: kpVar },
    }, whenClause);
    const corrVar = `corr_${slug(name)}`;
    const corrInput = { k: `@${kpVar}.public_key_pem`, e: endpoint, m: method };
    if (body !== undefined) corrInput.b = body;
    if (query !== undefined) corrInput.q = query;
    this.addNode(nodes, {
      id: `${prefixedId('T', name)}_corr`,
      kind: 'Transform',
      spec: { op: 'hash', alg: 'blake3' },
      in: corrInput,
      out: { var: corrVar },
    }, whenClause);
    const replyToVar = `reply_to_${slug(name)}`;
    this.addNode(nodes, {
      id: `${prefixedId('T', name)}_reply_to`,
      kind: 'Transform',
      spec: { op: 'concat' },
      in: { a: 'rpc:reply:', b: `@${corrVar}` },
      out: { var: replyToVar },
    }, whenClause);
    const payload = { method, corr: `@${corrVar}`, reply_to: `@${replyToVar}` };
    if (body !== undefined) payload.body = body;
    if (query !== undefined) payload.query = query;
    this.addNode(nodes, {
      id: prefixedId('P', `${name}_request`),
      kind: 'Publish',
      channel: `rpc:req:${endpoint}`,
      qos: 'at_least_once',
      payload,
    }, whenClause);
    const replyMsgVar = `${slug(name)}_reply`;
    this.addNode(nodes, {
      id: prefixedId('S', `${name}_reply`),
      kind: 'Subscribe',
      channel: `@${replyToVar}`,
      qos: 'at_least_once',
      filter: `@${corrVar}`,
      out: { var: replyMsgVar },
    }, whenClause);
    refs.set(name, `@${replyMsgVar}`);
  }

  expandBranch(branchDef, refs, nodes, whenClause) {
    const branchIdx = (this.branchIndex += 1);
    const label = `branch_${branchIdx}`;
    const { thenWhen, elseWhen } = this.compileCondition(branchDef.when, refs, nodes, label, whenClause);
    for (const step of branchDef.then ?? []) this.expandAction(step, refs, nodes, thenWhen);
    for (const step of branchDef.else ?? []) this.expandAction(step, refs, nodes, elseWhen);
  }

  expandAction(step, refs, nodes, whenClause) {
    const entries = Object.entries(step);
    if (entries.length !== 1) throw new Error('invalid monitor action');
    const [name, raw] = entries[0];
    if (name === 'branch') {
      this.expandBranch(raw, refs, nodes, whenClause);
      return;
    }
    const call = typeof raw === 'string' ? parseCall(raw) : parseCall(raw.call ?? raw);
    switch (call.macro) {
      case 'process.schedule':
        this.expandProcessSchedule(name, call, refs, nodes, whenClause);
        break;
      case 'transform.lookup':
        this.expandTransformLookup(name, call, refs, nodes, whenClause);
        break;
      case 'obs.emit_metric':
        this.expandEmitMetric(name, call, refs, nodes, whenClause);
        break;
      case 'interaction.request':
        this.expandInteractionRequest(name, call, refs, nodes, whenClause);
        break;
      default:
        throw new Error(`unsupported monitor macro: ${call.macro}`);
    }
  }

  compileMonitor(entry) {
    const monitorId = entry.monitor;
    const nodes = [];
    const refs = new Map();
    const onCall = parseCall(entry.on);
    let channel;
    switch (onCall.macro) {
      case 'obs.stream': {
        const arg = Array.isArray(onCall.args.__args) ? onCall.args.__args[0] : onCall.args.channel;
        if (!arg) throw new Error('obs.stream requires a channel');
        channel = arg;
        break;
      }
      case 'process.event': {
        const arg = Array.isArray(onCall.args.__args) ? onCall.args.__args[0] : onCall.args.name;
        if (!arg) throw new Error('process.event requires a name');
        channel = `process:event:${arg}`;
        break;
      }
      default:
        throw new Error(`unsupported monitor source: ${onCall.macro}`);
    }
    const eventVar = 'event_msg';
    this.addNode(nodes, {
      id: prefixedId('S', `${monitorId}_event`),
      kind: 'Subscribe',
      channel,
      qos: 'at_least_once',
      out: { var: eventVar },
    }, null);
    refs.set('event', `@${eventVar}`);

    let baseWhen = null;
    if (entry.when) {
      const { thenWhen } = this.compileCondition(entry.when, refs, nodes, `${monitorId}_when`, null);
      baseWhen = thenWhen;
    }

    for (const action of entry.then ?? []) this.expandAction(action, refs, nodes, baseWhen);

    return { monitor_id: monitorId, nodes };
  }

  build() {
    const monitors = [];
    for (const entry of this.definition.monitors ?? []) {
      this.conditionIndex = 0;
      this.branchIndex = 0;
      monitors.push(this.compileMonitor(entry));
    }
    const allNodes = monitors.flatMap((m) => m.nodes);
    return {
      bundle_id: this.bundleId,
      created_at: this.createdAt,
      effects: computeEffects(allNodes),
      monitors,
    };
  }
}

async function main() {
  const argv = process.argv.slice(2);
  if (argv.length < 2) usage();
  const [inputPath, outputPath] = argv;
  const raw = fs.readFileSync(inputPath, 'utf8');
  const processed = quoteCalls(raw);
  const def = parseYaml(processed);
  const compiler = new MonitorCompiler(def, outputPath);
  const l0 = compiler.build();
  fs.mkdirSync(path.dirname(outputPath), { recursive: true });
  fs.writeFileSync(outputPath, `${JSON.stringify(l0, null, 2)}\n`, 'utf8');
}

main().catch((err) => {
  console.error(err?.message ?? err);
  process.exit(1);
});
