import { readFile, writeFile, mkdir } from "node:fs/promises";
import path from "node:path";

import { canonicalize, canonicalJson } from "@tf-lang/utils";

export interface TraceSpec {
  name: string;
  version: string;
}

export interface TraceEvent {
  stepIndex: number;
  op: string;
  outcome: string;
  params: Record<string, unknown>;
  details: unknown;
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

export { canonicalJson } from "@tf-lang/utils";

function isRecord(x: unknown): x is Record<string, unknown> {
  return !!x && typeof x === "object" && !Array.isArray(x);
}

function pickString(obj: Record<string, unknown>, key: string): string | undefined {
  const value = obj[key];
  return typeof value === "string" ? value : undefined;
}

function pickNumber(obj: Record<string, unknown>, key: string): number | undefined {
  const value = obj[key];
  return typeof value === "number" && Number.isFinite(value) ? value : undefined;
}

function eventMetadata(event: TraceEvent): Record<string, unknown> {
  const details = event.details;
  if (!isRecord(details)) return {};
  switch (event.op) {
    case "copy":
      {
        const src = pickString(details, "src");
        const dest = pickString(details, "dest");
        return src && dest ? { src, dest } : {};
      }
    case "create_vm":
      {
        const id = pickString(details, "id");
        const image = pickString(details, "image");
        const cpus = pickNumber(details, "cpus");
        return id && image && typeof cpus === "number" ? { id, image, cpus } : {};
      }
    case "create_network":
      {
        const id = pickString(details, "id");
        const cidr = pickString(details, "cidr");
        return id && cidr ? { id, cidr } : {};
      }
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
