import {
  PLAN_GRAPH_VERSION,
  aggregateScores,
  ensureValidPlanGraph,
  freezePlanGraph,
  hashObject,
  stableId,
  stableSort,
  type PlanEdge,
  type PlanGraph,
  type PlanNode,
} from "@tf-lang/tf-plan-core";
import { scorePlanNode } from "@tf-lang/tf-plan-scoring";
import type { ScoreBreakdown } from "@tf-lang/tf-plan-core";
import type { RepoSignals } from "@tf-lang/tf-plan-scoring";
import type {
  EnumerateOptions,
  EnumeratedPlanNode,
  TfPlanComponent,
  TfPlanDesignChoice,
  TfPlanSpec,
} from "./types.js";

interface ChoiceEntry {
  readonly key: string;
  node: PlanNode;
  readonly component: TfPlanComponent;
  readonly choice: TfPlanDesignChoice;
  readonly score: ScoreBreakdown;
  readonly dependsOn: readonly string[];
  readonly excludes: readonly string[];
  readonly provides: readonly string[];
  readonly requires: readonly string[];
}

interface PartialSelection {
  readonly keys: readonly string[];
  readonly nodes: readonly ChoiceEntry[];
  readonly scores: readonly ScoreBreakdown[];
  readonly aggregated: ScoreBreakdown;
  readonly provides: readonly string[];
  readonly requires: readonly string[];
  readonly rationale: readonly string[];
}

const DEFAULT_SEED = 42;

function compareNodes(a: PlanNode, b: PlanNode): number {
  const totalDiff = b.score.total - a.score.total;
  if (Math.abs(totalDiff) > 1e-6) {
    return totalDiff > 0 ? 1 : -1;
  }
  const riskDiff = a.score.risk - b.score.risk;
  if (Math.abs(riskDiff) > 1e-6) {
    return riskDiff > 0 ? 1 : -1;
  }
  return a.nodeId.localeCompare(b.nodeId);
}

function compareSelections(a: PartialSelection, b: PartialSelection): number {
  const totalDiff = b.aggregated.total - a.aggregated.total;
  if (Math.abs(totalDiff) > 1e-6) {
    return totalDiff > 0 ? 1 : -1;
  }
  const riskDiff = a.aggregated.risk - b.aggregated.risk;
  if (Math.abs(riskDiff) > 1e-6) {
    return riskDiff > 0 ? 1 : -1;
  }
  return a.keys.join("|").localeCompare(b.keys.join("|"));
}

function mergeRepoSignals(base: RepoSignals | undefined, component: string, override: RepoSignals | undefined): RepoSignals | undefined {
  if (!base && !override) {
    return undefined;
  }
  const mergedComponentSignals = {
    ...(base?.componentSignals ?? {}),
    ...(override?.componentSignals ?? {}),
  };
  const existingSignals = mergedComponentSignals[component] ?? base?.componentSignals?.[component] ?? override?.componentSignals?.[component];
  const componentSignals = {
    ...existingSignals,
    ...(override?.componentSignals?.[component] ?? {}),
  };
  return {
    global: {
      ...base?.global,
      ...override?.global,
    },
    componentSignals: {
      ...mergedComponentSignals,
      [component]: {
        ...(base?.componentSignals?.[component] ?? {}),
        ...(override?.componentSignals?.[component] ?? {}),
        ...componentSignals,
      },
    },
  };
}

function toChoiceKey(component: string, choiceId: string): string {
  return `${component}:${choiceId}`;
}

function dedupeStrings(values: readonly string[]): readonly string[] {
  return Array.from(new Set(values)).sort();
}

function buildChoiceEntries(
  spec: TfPlanSpec,
  options: EnumerateOptions,
  seed: number
): Map<string, ChoiceEntry> {
  const map = new Map<string, ChoiceEntry>();
  const constraints = options.constraints;
  const baseSignals = spec.repoSignals;
  const components = stableSort([...spec.designSpace], (a, b) => a.component.localeCompare(b.component));

  for (const component of components) {
    const include = constraints?.include?.[component.component];
    const exclude = new Set(constraints?.exclude?.[component.component] ?? []);
    const choices = component.choices.filter((choice) => {
      if (include && !include.includes(choice.id)) {
        return false;
      }
      if (exclude.has(choice.id)) {
        return false;
      }
      return true;
    });
    if (choices.length === 0) {
      throw new Error(`no viable choices for component ${component.component}`);
    }

    for (const choice of choices) {
      const key = toChoiceKey(component.component, choice.id);
      const nodeId = stableId({
        scope: "choice",
        specId: spec.name,
        component: component.component,
        choice: choice.id,
        seed,
        version: PLAN_GRAPH_VERSION,
      });
      const repoSignals = mergeRepoSignals(baseSignals, component.component, choice.signals ? { componentSignals: { [component.component]: choice.signals } } : undefined);
      const score = scorePlanNode({
        component: component.component,
        choice: choice.title ?? choice.id,
        metadata: {
          tags: choice.tags,
          heuristics: choice.heuristics,
        },
        repoSignals,
      });
      const rationaleParts = [
        choice.summary ?? `Select ${choice.title ?? choice.id} for ${component.component}`,
      ];
      if (choice.rationale) {
        rationaleParts.push(choice.rationale);
      }
      rationaleParts.push(`Score total ${score.total.toFixed(2)}`);

      const entry: ChoiceEntry = {
        key,
        node: {
          nodeId,
          specId: spec.name,
          component: component.component,
          choice: choice.id,
          deps: [],
          rationale: rationaleParts.join("\n"),
          score,
        },
        component,
        choice,
        score,
        dependsOn: choice.dependsOn ?? [],
        excludes: choice.excludes ?? [],
        provides: choice.provides ?? [],
        requires: choice.requires ?? [],
      };
      map.set(key, entry);
    }
  }

  return map;
}

function resolveChoiceDependencies(entries: Map<string, ChoiceEntry>): PlanEdge[] {
  const edges: PlanEdge[] = [];
  for (const entry of entries.values()) {
    const deps: string[] = [];
    for (const dep of entry.dependsOn) {
      const target = entries.get(dep);
      if (target) {
        deps.push(target.node.nodeId);
        edges.push({ from: entry.node.nodeId, to: target.node.nodeId, kind: "depends_on" });
      }
    }
    const sortedDeps = stableSort(dedupeStrings(deps), (a, b) => a.localeCompare(b));
    entry.node = {
      ...entry.node,
      deps: sortedDeps,
    };
  }
  return edges;
}

function enumerateCombinations(
  components: readonly TfPlanComponent[],
  entries: Map<string, ChoiceEntry>,
  options: EnumerateOptions
): PartialSelection[] {
  const beamWidth = options.beamWidth;
  const sortedComponents = stableSort([...components], (a, b) => a.component.localeCompare(b.component));

  let partials: PartialSelection[] = [
    {
      keys: [],
      nodes: [],
      scores: [],
      aggregated: {
        total: 0,
        complexity: 0,
        risk: 0,
        perf: 0,
        devTime: 0,
        depsReady: 0,
        explain: [],
      },
      provides: [],
      requires: [],
      rationale: [],
    },
  ];

  for (const component of sortedComponents) {
    const next: PartialSelection[] = [];
    for (const partial of partials) {
      const seenKeys = new Set(partial.keys);
      for (const choice of component.choices) {
        const key = toChoiceKey(component.component, choice.id);
        const entry = entries.get(key);
        if (!entry || seenKeys.has(key)) {
          continue;
        }
        if (partial.nodes.some((node) => entry.excludes.includes(node.key) || node.excludes.includes(entry.key))) {
          continue;
        }
        const scores = [...partial.scores, entry.score];
        const aggregated = scores.length === 1 ? entry.score : aggregateScores(scores);
        const provides = dedupeStrings([...partial.provides, ...entry.provides]);
        const requires = [...partial.requires, ...entry.requires];
        const rationale = [...partial.rationale, entry.node.rationale];
        next.push({
          keys: [...partial.keys, key],
          nodes: [...partial.nodes, entry],
          scores,
          aggregated,
          provides,
          requires,
          rationale,
        });
      }
    }
    partials = stableSort(next, compareSelections);
    if (typeof beamWidth === "number" && beamWidth > 0) {
      partials = partials.slice(0, beamWidth);
    }
  }

  return partials;
}

function filterSelections(partials: readonly PartialSelection[], constraints: EnumerateOptions["constraints"]): PartialSelection[] {
  const filtered: PartialSelection[] = [];
  const requireCapabilities = new Set(constraints?.requires ?? []);

  for (const partial of partials) {
    const provides = new Set(partial.provides);
    const keys = new Set(partial.keys);
    const hasAllDepends = partial.nodes.every((entry) => entry.dependsOn.every((dep) => keys.has(dep)));
    const hasAllCapabilities = [...partial.requires].every((cap) => provides.has(cap));
    const satisfiesConstraint = [...requireCapabilities].every((cap) => provides.has(cap) || keys.has(cap));
    if (hasAllDepends && hasAllCapabilities && satisfiesConstraint) {
      filtered.push(partial);
    }
  }

  return filtered;
}

export function enumeratePlanGraph(spec: TfPlanSpec, options: EnumerateOptions = {}): PlanGraph {
  if (!spec.designSpace || spec.designSpace.length === 0) {
    throw new Error("tf-plan spec requires at least one component in designSpace");
  }
  const seed = options.seed ?? DEFAULT_SEED;
  const entries = buildChoiceEntries(spec, options, seed);
  const dependencyEdges = resolveChoiceDependencies(entries);
  const components = stableSort([...spec.designSpace], (a, b) => a.component.localeCompare(b.component));
  const selections = enumerateCombinations(components, entries, options);
  const viableSelections = filterSelections(selections, options.constraints);
  const limitedSelections = typeof options.maxNodes === "number" && options.maxNodes > 0 ? viableSelections.slice(0, options.maxNodes) : viableSelections;

  if (limitedSelections.length === 0) {
    throw new Error("enumeration produced no viable plan branches");
  }

  const planNodes: PlanNode[] = [];
  const planEdges: PlanEdge[] = [...dependencyEdges];

  for (const selection of limitedSelections) {
    const sortedEntries = stableSort(selection.nodes, (a, b) => compareNodes(a.node, b.node));
    const choiceString = sortedEntries
      .map((entry) => `${entry.component.component}=${entry.choice.id}`)
      .join("|");
    const nodeId = stableId({
      scope: "plan",
      specId: spec.name,
      component: "plan",
      choice: choiceString,
      seed,
      version: PLAN_GRAPH_VERSION,
    });
    const deps = sortedEntries.map((entry) => entry.node.nodeId);
    planEdges.push(
      ...sortedEntries.map((entry) => ({
        from: nodeId,
        to: entry.node.nodeId,
        kind: "composes" as const,
      }))
    );
    const rationale = [
      `Branch covers ${choiceString}.`,
      ...selection.rationale,
      `Aggregate score ${selection.aggregated.total.toFixed(2)} with ${selection.aggregated.explain.length} contributing factors.`,
    ].join("\n");
    planNodes.push({
      nodeId,
      specId: spec.name,
      component: "plan",
      choice: choiceString,
      deps,
      rationale,
      score: selection.aggregated,
    });
  }

  const componentNodes = Array.from(entries.values()).map((entry) => entry.node);
  const nodes = stableSort([...componentNodes, ...planNodes], compareNodes);
  const edges = stableSort(planEdges, (a, b) => {
    const fromDiff = a.from.localeCompare(b.from);
    if (fromDiff !== 0) return fromDiff;
    const toDiff = a.to.localeCompare(b.to);
    if (toDiff !== 0) return toDiff;
    return a.kind.localeCompare(b.kind);
  });

  const graph: PlanGraph = {
    nodes,
    edges,
    meta: {
      seed,
      specHash: hashObject(spec),
      specId: spec.name,
      version: PLAN_GRAPH_VERSION,
    },
  };

  return freezePlanGraph(ensureValidPlanGraph(graph));
}

export function toEnumeratedNodes(entries: Map<string, ChoiceEntry>): EnumeratedPlanNode[] {
  return Array.from(entries.values()).map((entry) => ({
    nodeId: entry.node.nodeId,
    choice: entry.choice,
    component: entry.component,
  }));
}
