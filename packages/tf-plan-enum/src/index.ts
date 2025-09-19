import Ajv from 'ajv';
import type { Schema } from 'ajv';
import specSchema from '../../../schema/tf-spec.schema.json' with { type: "json" };
import {
  computeSpecHash,
  createScore,
  freezePlanGraph,
  PlanGraph,
  PlanNode,
  seedRng,
  stableId,
  stableSort,
} from '@tf-lang/tf-plan-core';
import { scorePlanNode } from '@tf-lang/tf-plan-scoring';

export interface EnumerateOptions {
  readonly seed?: number;
  readonly beamWidth?: number;
  readonly constraints?: {
    readonly include?: Record<string, readonly string[]>;
    readonly exclude?: Record<string, readonly string[]>;
    readonly maxNodes?: number;
  };
  readonly version?: string;
}

export interface TfSpecStep {
  readonly op: string;
  readonly params: Record<string, unknown>;
}

export interface TfSpec {
  readonly version: string;
  readonly name: string;
  readonly steps: readonly TfSpecStep[];
}

const ajv = new Ajv({ strict: false, allErrors: true });
const validateSpec = ajv.compile(specSchema as Schema);

function assertSpec(input: unknown): TfSpec {
  if (!validateSpec(input)) {
    const message = validateSpec.errors?.map((err) => `${err.instancePath} ${err.message}`).join('; ');
    throw new Error(`Invalid spec: ${message ?? 'unknown error'}`);
  }
  return input as TfSpec;
}

function enumerateChoices(step: TfSpecStep): readonly string[] {
  switch (step.op) {
    case 'copy':
      return ['direct', 'streaming', 'cached'];
    case 'create_vm':
      return ['aws_t3.micro', 'gcp_e2.small', 'azure_b2s'];
    case 'create_network':
      return ['10.0.0.0/24', '192.168.0.0/24', '172.16.0.0/16'];
    default:
      return ['default'];
  }
}

function applyConstraints(component: string, choices: readonly string[], options?: EnumerateOptions): readonly string[] {
  let filtered = [...choices];
  const include = options?.constraints?.include?.[component];
  if (include && include.length > 0) {
    filtered = filtered.filter((choice) => include.includes(choice));
  }
  const exclude = new Set(options?.constraints?.exclude?.[component] ?? []);
  if (exclude.size > 0) {
    filtered = filtered.filter((choice) => !exclude.has(choice));
  }
  return filtered;
}

interface CombinationContext {
  readonly spec: TfSpec;
  readonly seed: number;
  readonly version: string;
  readonly options: EnumerateOptions;
}

function buildNode(
  context: CombinationContext,
  components: readonly { component: string; choice: string }[],
): PlanNode {
  const explain: string[] = [];
  let complexity = 0;
  let risk = 0;
  let perf = 0;
  let devTime = 0;
  let depsReady = 0;

  for (const { component, choice } of components) {
    const score = scorePlanNode({ component, choice });
    explain.push(`${component}: ${score.explain.join('; ')}`);
    complexity += score.complexity;
    risk += score.risk;
    perf += score.perf;
    devTime += score.devTime;
    depsReady += score.depsReady;
  }

  const finalScore = createScore({
    complexity,
    risk,
    perf,
    devTime,
    depsReady,
    explain,
  });

  const specId = context.spec.name;
  const choiceSummary = components.map((item) => `${item.component}=${item.choice}`).join(', ');
  const nodeId = stableId({
    specId,
    component: 'plan',
    choice: choiceSummary,
    seed: context.seed,
    version: context.version,
  });

  const node: PlanNode = {
    nodeId,
    specId,
    component: 'plan',
    choice: choiceSummary,
    deps: components.map((item) => item.component),
    rationale: `Plan covering ${components.length} components: ${choiceSummary}`,
    score: finalScore,
  };

  return node;
}

function combine(
  context: CombinationContext,
  components: readonly { name: string; choices: readonly string[] }[],
  index: number,
  current: readonly { component: string; choice: string }[],
  results: PlanNode[],
) {
  if (index >= components.length) {
    const node = buildNode(context, current);
    results.push(node);
    return;
  }

  const component = components[index];
  for (const choice of component.choices) {
    combine(context, components, index + 1, [...current, { component: component.name, choice }], results);
  }
}

export function enumeratePlanGraph(specInput: unknown, options: EnumerateOptions = {}): PlanGraph {
  const spec = assertSpec(specInput);
  const seed = options.seed ?? 42;
  const version = options.version ?? '1.0.0';
  const specHash = computeSpecHash(spec);
  const rng = seedRng(seed);

  const components = spec.steps.map((step, index) => {
    const component = `${index + 1}:${step.op}`;
    const baseChoices = enumerateChoices(step);
    const choices = applyConstraints(component, baseChoices, options);
    if (choices.length === 0) {
      throw new Error(`No viable choices for component ${component}`);
    }
    return { name: component, choices };
  });

  const nodesBuffer: PlanNode[] = [];
  combine({ spec, seed: rng.seed, version, options }, components, 0, [], nodesBuffer);

  let nodes = nodesBuffer;

  if (options.beamWidth && options.beamWidth > 0 && nodes.length > options.beamWidth) {
    nodes = stableSort(nodes, (a, b) => {
      if (a.score.total !== b.score.total) {
        return b.score.total - a.score.total;
      }
      if (a.score.risk !== b.score.risk) {
        return a.score.risk - b.score.risk;
      }
      return a.nodeId.localeCompare(b.nodeId);
    }).slice(0, options.beamWidth);
  }

  const maxNodes = options.constraints?.maxNodes;
  if (typeof maxNodes === 'number' && nodes.length > maxNodes) {
    nodes = nodes.slice(0, maxNodes);
  }

  nodes = stableSort(nodes, (a, b) => {
    if (a.score.total !== b.score.total) {
      return b.score.total - a.score.total;
    }
    if (a.score.risk !== b.score.risk) {
      return a.score.risk - b.score.risk;
    }
    return a.nodeId.localeCompare(b.nodeId);
  });

  const graph: PlanGraph = {
    nodes,
    edges: [],
    meta: {
      seed: rng.seed,
      specHash,
      version,
    },
  };

  return freezePlanGraph(graph);
}
