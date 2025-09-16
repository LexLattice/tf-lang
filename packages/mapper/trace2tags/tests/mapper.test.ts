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
