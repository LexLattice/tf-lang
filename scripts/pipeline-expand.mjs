#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { parse as parseYaml } from 'yaml';

function usage() {
  console.error('usage: pipeline-expand <input.l2.yaml> <output.l0.json>');
  process.exit(2);
}

function quoteCalls(src) {
  const lines = src.split(/\r?\n/);
  const out = [];
  for (let i = 0; i < lines.length; i += 1) {
    const line = lines[i];
    const match = line.match(/^(\s*-\s+[A-Za-z0-9_]+:\s*)([A-Za-z0-9_.]+\()(.*)$/);
    if (match) {
      let call = match[2] + match[3];
      let depth = (match[2].match(/\(/g) || []).length - (match[2].match(/\)/g) || []).length;
      depth += (match[3].match(/\(/g) || []).length - (match[3].match(/\)/g) || []).length;
      while (depth > 0 && i + 1 < lines.length) {
        const next = lines[++i];
        call += `\n${next.trim()}`;
        depth += (next.match(/\(/g) || []).length - (next.match(/\)/g) || []).length;
      }
      call = call.replace(/\s*\n\s*/g, ' ');
      call = call.replace(/"/g, '\\"');
      out.push(`${match[1]}"${call}"`);
      continue;
    }
    out.push(line);
  }
  return out.join('\n');
}

function parseCall(str) {
  const match = str.match(/^([A-Za-z0-9_.]+)\((.*)\)$/);
  if (!match) throw new Error(`invalid call syntax: ${str}`);
  const [, macro, argsRaw] = match;
  const trimmed = argsRaw.trim();
  if (!trimmed) return { macro, args: {} };
  if (trimmed.includes(':')) return { macro, args: parseYaml(`{ ${trimmed} }`) };
  const positional = parseYaml(`[${trimmed}]`);
  return { macro, args: { __args: positional } };
}

function slug(value) {
  return String(value)
    .replace(/[^A-Za-z0-9_]+/g, '_')
    .replace(/_{2,}/g, '_')
    .replace(/^_+|_+$/g, '')
    .toLowerCase();
}

function id(prefix, name) {
  return `${prefix}_${slug(name)}`;
}

const ALLOWED_KINDS = new Set(['Transform', 'Publish', 'Subscribe', 'Keypair']);

function computeEffects(nodes) {
  const seen = new Set();
  for (const node of nodes) {
    switch (node.kind) {
      case 'Publish':
        seen.add('Outbound');
        break;
      case 'Subscribe':
        seen.add('Inbound');
        break;
      case 'Keypair':
        seen.add('Entropy');
        break;
      case 'Transform':
        seen.add('Pure');
        break;
      default:
        throw new Error(`unsupported kernel kind: ${node.kind}`);
    }
  }
  const order = ['Outbound', 'Inbound', 'Entropy', 'Pure'];
  const values = order.filter((effect) => seen.has(effect));
  if (values.length === 0) return 'Pure';
  return values.join('+');
}

class PipelineBuilder {
  constructor(def, existing) {
    this.pipelineId = def.pipeline;
    this.description = def.description ?? '';
    this.createdAt = existing?.created_at ?? new Date().toISOString();
    this.nodes = [];
    this.refs = new Map();
    this.msgInfo = new Map();
    this.branchIndex = 0;
  }

  registerRef(name, value, { synonyms = [] } = {}) {
    const entries = new Set([name, ...synonyms]);
    for (const entry of entries) {
      if (!entry) continue;
      const variants = new Set([entry, slug(entry)]);
      for (const variant of variants) {
        if (!variant) continue;
        this.refs.set(variant, value);
      }
    }
  }

  resolveRef(ref) {
    if (typeof ref !== 'string' || !ref.startsWith('@')) return ref;
    const pathExpr = ref.slice(1);
    const [head, ...rest] = pathExpr.split('.');
    const mapped = this.refs.get(head) ?? `@${head}`;
    if (rest.length === 0) return mapped;
    const suffix = rest.join('.');
    if (mapped.startsWith('@')) return `${mapped}.${suffix}`;
    return `@${mapped}.${suffix}`;
  }

  resolveValue(value) {
    if (Array.isArray(value)) return value.map((v) => this.resolveValue(v));
    if (value && typeof value === 'object') {
      const out = {};
      for (const [k, v] of Object.entries(value)) out[k] = this.resolveValue(v);
      return out;
    }
    if (typeof value === 'string') return this.resolveRef(value);
    return value;
  }

  addNode(node, whenClause) {
    if (!ALLOWED_KINDS.has(node.kind)) {
      throw new Error(`invalid kernel kind: ${node.kind}`);
    }
    const finalNode = { ...node };
    if (whenClause) finalNode.when = whenClause;
    this.nodes.push(finalNode);
  }

  addInput(name, call) {
    if (call.macro !== 'interaction.receive') throw new Error(`unsupported input macro: ${call.macro}`);
    const endpoint = call.args.endpoint;
    const qos = call.args.qos ?? 'at_least_once';
    const parts = String(endpoint).split('/').filter(Boolean);
    const resource = parts.length >= 2 ? parts[1] : parts[parts.length - 1] ?? name;
    const varName = `${slug(resource)}_msg`;
    const nodeId = `S_${slug(name)}_${slug(resource)}`;
    this.addNode({
      id: nodeId,
      kind: 'Subscribe',
      channel: `rpc:req:${endpoint}`,
      qos,
      out: { var: varName },
    });
    this.registerRef(name, `@${varName}`, { synonyms: [`${name}_msg`, `${slug(name)}_msg`] });
    this.msgInfo.set(name, { varName });
  }

  addTransform(name, spec, input, outVar, whenClause) {
    this.addNode({
      id: id('T', name),
      kind: 'Transform',
      spec,
      in: input,
      out: { var: outVar },
    }, whenClause);
    const base = slug(name);
    const aliases = new Set([
      `${name}_value`,
      `${name}_out`,
      `${base}_value`,
      `${base}_out`,
      outVar,
    ]);
    this.registerRef(name, `@${outVar}`, { synonyms: Array.from(aliases) });
  }

  expandValidate(name, call, whenClause) {
    const schema = call.args.schema;
    const input = this.resolveValue(call.args.input);
    const varName = `${slug(name)}_value`;
    this.addTransform(name, { op: 'jsonschema.validate', schema }, { value: input }, varName, whenClause);
  }

  expandModelInfer(name, call, whenClause) {
    const model = call.args.model;
    const features = this.resolveValue(call.args.input ?? call.args.features ?? call.args.payload);
    const varName = `${slug(name)}_value`;
    this.addTransform(name, { op: 'model_infer', model }, { features }, varName, whenClause);
  }

  expandPolicyEval(name, call, whenClause) {
    const policy = call.args.policy;
    const input = this.resolveValue(call.args.input ?? {});
    const varName = `${slug(name)}_value`;
    this.addTransform(name, { op: 'policy_eval', policy }, { input }, varName, whenClause);
  }

  expandGenericTransform(name, call, whenClause) {
    const [, op = 'custom'] = call.macro.split('.', 2);
    const spec = { op };
    const inputKeys = new Set(['input', 'value', 'left', 'right', 'lhs', 'rhs', 'data', 'payload']);
    const input = {};
    for (const [key, raw] of Object.entries(call.args)) {
      const resolved = this.resolveValue(raw);
      if (inputKeys.has(key)) {
        input[key] = resolved;
      } else {
        spec[key] = resolved;
      }
    }
    const inObject = Object.keys(input).length > 0 ? input : {};
    const varName = `${slug(name)}_value`;
    this.addTransform(name, spec, inObject, varName, whenClause);
  }

  expandRequest(name, call, whenClause) {
    const endpoint = call.args.endpoint;
    const method = call.args.method ?? 'POST';
    const body = call.args.body ? this.resolveValue(call.args.body) : undefined;
    const query = call.args.query ? this.resolveValue(call.args.query) : undefined;
    const kpVar = `kp_${slug(name)}`;
    this.addNode({
      id: id('K', name),
      kind: 'Keypair',
      algorithm: 'Ed25519',
      out: { var: kpVar },
    }, whenClause);
    const corrVar = `corr_${slug(name)}`;
    const corrInput = {
      k: `@${kpVar}.public_key_pem`,
      e: endpoint,
      m: method,
    };
    if (body !== undefined) corrInput.b = body;
    if (query !== undefined) corrInput.q = query;
    this.addNode({
      id: `${id('T', name)}_corr`,
      kind: 'Transform',
      spec: { op: 'hash', alg: 'blake3' },
      in: corrInput,
      out: { var: corrVar },
    }, whenClause);
    const replyVar = `reply_to_${slug(name)}`;
    this.addNode({
      id: `${id('T', name)}_reply_to`,
      kind: 'Transform',
      spec: { op: 'concat' },
      in: { a: 'rpc:reply:', b: `@${corrVar}` },
      out: { var: replyVar },
    }, whenClause);
    const payload = {
      method,
      corr: `@${corrVar}`,
      reply_to: `@${replyVar}`,
    };
    if (body !== undefined) payload.body = body;
    if (query !== undefined) payload.query = query;
    this.addNode({
      id: id('P', `${name}_request`),
      kind: 'Publish',
      channel: `rpc:req:${endpoint}`,
      qos: 'at_least_once',
      payload,
    }, whenClause);
    const replyMsgVar = `${slug(name)}_reply`;
    this.addNode({
      id: id('S', `${name}_reply`),
      kind: 'Subscribe',
      channel: `@${replyVar}`,
      qos: 'at_least_once',
      filter: `@${corrVar}`,
      out: { var: replyMsgVar },
    }, whenClause);
    this.registerRef(name, `@${replyMsgVar}`, { synonyms: [`${name}_reply`, `${slug(name)}_reply`] });
  }

  expandEmitMetric(name, call, whenClause) {
    const metricName = call.args.name;
    const value = this.resolveValue(call.args.value ?? 1);
    const tags = call.args.tags ? this.resolveValue(call.args.tags) : undefined;
    const payload = { value, unit: 'count' };
    if (tags) payload.tags = tags;
    this.addNode({
      id: id('P', name),
      kind: 'Publish',
      channel: `metric:${metricName}`,
      qos: 'at_least_once',
      payload,
    }, whenClause);
  }

  expandReply(name, call, whenClause) {
    const toExpr = this.resolveRef(call.args.to);
    const base = toExpr.startsWith('@') ? toExpr : `@${toExpr}`;
    const channel = `${base}.reply_to`;
    const payload = { corr: `${base}.corr` };
    for (const [k, v] of Object.entries(call.args)) {
      if (k === 'to') continue;
      payload[k] = this.resolveValue(v);
    }
    this.addNode({
      id: id('P', name),
      kind: 'Publish',
      channel,
      qos: 'at_least_once',
      payload,
    }, whenClause);
  }

  expandRecord(name, call, whenClause) {
    const kindValue = call.args.kind;
    const payloadExpr = this.resolveValue(call.args.payload);
    const digestVar = `${slug(name)}_digest_value`;
    this.addNode({
      id: `${id('T', name)}_digest`,
      kind: 'Transform',
      spec: { op: 'digest', alg: 'blake3' },
      in: { kind: kindValue, payload: payloadExpr, ts: this.createdAt },
      out: { var: digestVar },
    }, whenClause);
    const idVar = `${slug(name)}_id_value`;
    this.addNode({
      id: `${id('T', name)}_id`,
      kind: 'Transform',
      spec: { op: 'encode_base58' },
      in: { value: `@${digestVar}` },
      out: { var: idVar },
    }, whenClause);
    this.addNode({
      id: id('P', name),
      kind: 'Publish',
      channel: 'policy:record',
      qos: 'at_least_once',
      payload: { record_id: `@${idVar}`, kind: kindValue, payload: payloadExpr, ts: this.createdAt },
    }, whenClause);
  }

  expandStep(name, call, whenClause) {
    switch (call.macro) {
      case 'transform.validate':
        this.expandValidate(name, call, whenClause);
        break;
      case 'transform.model_infer':
        this.expandModelInfer(name, call, whenClause);
        break;
      case 'policy.evaluate':
        this.expandPolicyEval(name, call, whenClause);
        break;
      case 'interaction.request':
        this.expandRequest(name, call, whenClause);
        break;
      case 'obs.emit_metric':
        this.expandEmitMetric(name, call, whenClause);
        break;
      case 'interaction.reply':
        this.expandReply(name, call, whenClause);
        break;
      case 'policy.record_decision':
        this.expandRecord(name, call, whenClause);
        break;
      default:
        if (call.macro.startsWith('transform.')) {
          this.expandGenericTransform(name, call, whenClause);
          break;
        }
        throw new Error(`unsupported macro: ${call.macro}`);
    }
  }

  expandBranch(branchDef, whenClause) {
    const cond = branchDef.when;
    const eqMatch = typeof cond === 'string' ? cond.match(/^@([A-Za-z0-9_.]+)\s*==\s*'([^']+)'$/) : null;
    if (!eqMatch) throw new Error(`unsupported branch condition: ${cond}`);
    const branchIdx = (this.branchIndex += 1);
    const condVar = `branch_${branchIdx}_value`;
    const leftExpr = this.resolveRef(`@${eqMatch[1]}`);
    const rightValue = eqMatch[2];
    this.addNode({
      id: `T_branch_${branchIdx}`,
      kind: 'Transform',
      spec: { op: 'eq' },
      in: { left: leftExpr, right: rightValue },
      out: { var: condVar },
    }, whenClause);
    const thenWhen = `@${condVar}`;
    const elseWhen = { op: 'not', var: condVar };
    for (const step of branchDef.then ?? []) this.processStep(step, thenWhen);
    for (const step of branchDef.else ?? []) this.processStep(step, elseWhen);
  }

  processStep(step, whenClause) {
    const entries = Object.entries(step);
    if (entries.length !== 1) throw new Error('invalid step entry');
    const [name, value] = entries[0];
    if (name === 'branch') {
      this.expandBranch(value, whenClause);
      return;
    }
    const call = typeof value === 'string' ? parseCall(value) : parseCall(value.call ?? value);
    this.expandStep(name, call, whenClause);
  }

  build(def) {
    for (const input of def.inputs ?? []) {
      const [name, value] = Object.entries(input)[0];
      const call = parseCall(typeof value === 'string' ? value : value.call ?? value);
      this.addInput(name, call);
    }
    for (const step of def.steps ?? []) this.processStep(step, null);
    for (const output of def.outputs ?? []) this.processStep(output, null);
    return {
      pipeline_id: this.pipelineId,
      created_at: this.createdAt,
      effects: computeEffects(this.nodes),
      nodes: this.nodes,
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
  let existing = null;
  if (fs.existsSync(outputPath)) {
    try {
      existing = JSON.parse(fs.readFileSync(outputPath, 'utf8'));
    } catch {
      existing = null;
    }
  }
  const builder = new PipelineBuilder(def, existing);
  const l0 = builder.build(def);
  fs.mkdirSync(path.dirname(outputPath), { recursive: true });
  fs.writeFileSync(outputPath, `${JSON.stringify(l0, null, 2)}\n`, 'utf8');
}

main().catch((err) => {
  console.error(err?.message ?? err);
  process.exit(1);
});
