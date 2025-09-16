import { mkdtempSync, rmSync, readFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";

import { describe, expect, it } from "vitest";

import {
  canonicalJson,
  generateArtifacts,
  loadTraces,
  mapTraces,
} from "../src/index.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const traceFixture = path.join(here, "../fixtures/traces.jsonl");

describe("trace → tags mapper", () => {
  it("loads JSONL traces", async () => {
    const traces = await loadTraces(traceFixture);
    expect(traces).toHaveLength(1);
    expect(traces[0].events).toHaveLength(3);
  });

  it("maps events to deterministic tags", async () => {
    const traces = await loadTraces(traceFixture);
    const tags = mapTraces(traces);
    expect(tags).toMatchObject([
      { tag: "resource.copy", stepIndex: 0 },
      { tag: "resource.vm", stepIndex: 1 },
      { tag: "resource.network", stepIndex: 2 },
    ]);
  });

  it("falls back to empty metadata when details are malformed", () => {
    const tags = mapTraces([
      {
        spec: { name: "bad", version: "0.1" },
        events: [
          {
            stepIndex: 0,
            op: "create_vm",
            outcome: "success",
            params: {},
            details: { id: 42, image: 17, cpus: "two" },
          },
          {
            stepIndex: 1,
            op: "copy",
            outcome: "success",
            params: {},
            details: "not an object",
          },
        ],
      },
    ]);
    expect(tags).toHaveLength(2);
    const [first, second] = tags;
    expect(first.metadata).toEqual({});
    expect(second.metadata).toEqual({});
    expect(first.stepIndex).toBeLessThanOrEqual(second.stepIndex);
  });

  it("writes canonical artifacts", async () => {
    const dir = mkdtempSync(path.join(tmpdir(), "trace-tags-"));
    try {
      const outPath = path.join(dir, "trace-tags.json");
      await generateArtifacts({ tracePath: traceFixture, outPath });
      const content = readFileSync(outPath, "utf-8");
      expect(content.endsWith("\n")).toBe(true);
      const normalized = canonicalJson(JSON.parse(content));
      expect(normalized).toBe(content);
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });
});
