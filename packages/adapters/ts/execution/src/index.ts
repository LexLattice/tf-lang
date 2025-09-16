import { readFile, writeFile, mkdir } from "node:fs/promises";
import path from "node:path";

import { canonicalJson } from "@tf-lang/utils";

import type { TfSpec } from "tf-lang-l0";

export { canonicalJson } from "@tf-lang/utils";

export interface ExecutionOptions {
  vmPrefix?: string;
  networkPrefix?: string;
}

export interface TraceEvent {
  stepIndex: number;
  op: string;
  outcome: "success";
  params: Record<string, unknown>;
  details: Record<string, unknown>;
}

export interface ResourceSummary {
  copies: Array<{ src: string; dest: string }>;
  vms: Array<{ id: string; image: string; cpus: number }>;
  networks: Array<{ id: string; cidr: string }>;
}

export interface ExecutionTrace {
  spec: {
    name: string;
    version: string;
  };
  events: TraceEvent[];
  summary: ResourceSummary;
}

export function isCopyStep(step: TfSpec["steps"][number]): step is {
  op: "copy";
  params: { src: string; dest: string };
} {
  return step.op === "copy";
}

export function isCreateVmStep(step: TfSpec["steps"][number]): step is {
  op: "create_vm";
  params: { image: string; cpus: number };
} {
  return step.op === "create_vm";
}

export function isCreateNetworkStep(step: TfSpec["steps"][number]): step is {
  op: "create_network";
  params: { cidr: string };
} {
  return step.op === "create_network";
}

const DEFAULT_PREFIXES = {
  vm: "vm",
  network: "net",
};

function nextId(prefix: string, counter: number): string {
  return `${prefix}-${counter}`;
}

export function executeSpec(spec: TfSpec, options: ExecutionOptions = {}): ExecutionTrace {
  const events: TraceEvent[] = [];
  const summary: ResourceSummary = { copies: [], vms: [], networks: [] };
  let vmCount = 0;
  let networkCount = 0;

  spec.steps.forEach((step, index) => {
    if (isCopyStep(step)) {
      const details = { src: step.params.src, dest: step.params.dest };
      events.push({
        stepIndex: index,
        op: step.op,
        outcome: "success",
        params: { ...details },
        details,
      });
      summary.copies.push(details);
      return;
    }
    if (isCreateVmStep(step)) {
      vmCount += 1;
      const id = nextId(options.vmPrefix ?? DEFAULT_PREFIXES.vm, vmCount);
      const details = {
        id,
        image: step.params.image,
        cpus: step.params.cpus,
      };
      events.push({
        stepIndex: index,
        op: step.op,
        outcome: "success",
        params: { ...step.params },
        details,
      });
      summary.vms.push(details);
      return;
    }
    if (isCreateNetworkStep(step)) {
      networkCount += 1;
      const id = nextId(options.networkPrefix ?? DEFAULT_PREFIXES.network, networkCount);
      const details = { id, cidr: step.params.cidr };
      events.push({
        stepIndex: index,
        op: step.op,
        outcome: "success",
        params: { ...step.params },
        details,
      });
      summary.networks.push(details);
      return;
    }
    throw new Error(`E_ADAPTER_UNKNOWN_OP ${step.op}`);
  });

  return {
    spec: { name: spec.name, version: spec.version },
    events,
    summary,
  };
}

export async function loadSpec(filePath: string): Promise<TfSpec> {
  const text = await readFile(filePath, "utf-8");
  return JSON.parse(text) as TfSpec;
}

export interface ArtifactOptions {
  outDir: string;
  specPath: string;
}

export async function writeTraceArtifacts(options: ArtifactOptions): Promise<void> {
  const { outDir, specPath } = options;
  const spec = await loadSpec(specPath);
  const trace = executeSpec(spec);
  await mkdir(outDir, { recursive: true });
  const target = path.join(outDir, "adapter-ts-trace.json");
  await writeFile(target, canonicalJson(trace), "utf-8");
}
