import { readFile, writeFile, mkdir } from "node:fs/promises";
import path from "node:path";

export interface TraceSpec {
  name: string;
  version: string;
}

export interface TraceEvent {
  stepIndex: number;
  op: string;
  outcome: string;
  params: Record<string, unknown>;
  details: Record<string, unknown>;
}

export interface ExecutionTrace {
  spec: TraceSpec;
  events: TraceEvent[];
}

export interface TraceTag {
  spec: string;
  version: string;
  stepIndex: number;
  op: string;
  tag: string;
  metadata: Record<string, unknown>;
}

function canonicalize(value: unknown): unknown {
  if (value === null) return null;
  if (Array.isArray(value)) {
    return value.map((item) => canonicalize(item));
  }
  if (typeof value === "object") {
    const entries = Object.entries(value as Record<string, unknown>)
      .map(([k, v]) => [k, canonicalize(v)] as const)
      .sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0));
    const out: Record<string, unknown> = {};
    for (const [k, v] of entries) out[k] = v;
    return out;
  }
  return value;
}

export function canonicalJson(value: unknown): string {
  return `${JSON.stringify(canonicalize(value), null, 2)}\n`;
}

function eventMetadata(event: TraceEvent): Record<string, unknown> {
  switch (event.op) {
    case "copy":
      return {
        src: event.details.src,
        dest: event.details.dest,
      };
    case "create_vm":
      return {
        id: event.details.id,
        image: event.details.image,
        cpus: event.details.cpus,
      };
    case "create_network":
      return {
        id: event.details.id,
        cidr: event.details.cidr,
      };
    default:
      return {};
  }
}

function eventTag(op: string): string {
  switch (op) {
    case "copy":
      return "resource.copy";
    case "create_vm":
      return "resource.vm";
    case "create_network":
      return "resource.network";
    default:
      return "resource.unknown";
  }
}

export function mapTrace(trace: ExecutionTrace): TraceTag[] {
  const tags: TraceTag[] = [];
  trace.events
    .filter((event) => event.outcome === "success")
    .forEach((event) => {
      tags.push({
        spec: trace.spec.name,
        version: trace.spec.version,
        stepIndex: event.stepIndex,
        op: event.op,
        tag: eventTag(event.op),
        metadata: canonicalize(eventMetadata(event)) as Record<string, unknown>,
      });
    });
  tags.sort((a, b) => a.stepIndex - b.stepIndex || a.tag.localeCompare(b.tag));
  return tags;
}

export function mapTraces(traces: ExecutionTrace[]): TraceTag[] {
  const tags = traces.flatMap((trace) => mapTrace(trace));
  tags.sort((a, b) => {
    const name = a.spec.localeCompare(b.spec);
    if (name !== 0) return name;
    const step = a.stepIndex - b.stepIndex;
    if (step !== 0) return step;
    return a.tag.localeCompare(b.tag);
  });
  return tags;
}

export async function loadTraces(filePath: string): Promise<ExecutionTrace[]> {
  const text = await readFile(filePath, "utf-8");
  if (filePath.endsWith(".jsonl")) {
    return text
      .split(/\r?\n/)
      .map((line) => line.trim())
      .filter((line) => line.length > 0)
      .map((line) => JSON.parse(line) as ExecutionTrace);
  }
  const parsed = JSON.parse(text);
  if (Array.isArray(parsed)) {
    return parsed as ExecutionTrace[];
  }
  return [parsed as ExecutionTrace];
}

export async function writeTagsFile(filePath: string, tags: TraceTag[]): Promise<void> {
  await mkdir(path.dirname(filePath), { recursive: true });
  await writeFile(filePath, canonicalJson(tags), "utf-8");
}

export interface ArtifactOptions {
  tracePath: string;
  outPath?: string;
}

export async function generateArtifacts(options: ArtifactOptions): Promise<void> {
  const traces = await loadTraces(options.tracePath);
  const tags = mapTraces(traces);
  const target = options.outPath ?? path.resolve("out/t2/trace-tags.json");
  await writeTagsFile(target, tags);
}
