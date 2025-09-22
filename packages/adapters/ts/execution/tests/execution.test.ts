// @tf-test kind=product area=adapters speed=fast deps=node

import { readFileSync, mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";

import { describe, expect, it } from "vitest";

import {
  executeSpec,
  loadSpec,
  writeTraceArtifacts,
} from "../src/index.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const specPath = path.join(here, "../fixtures/sample-spec.json");
const tracePath = path.join(here, "../fixtures/sample-trace.json");

function readJson(file: string): unknown {
  return JSON.parse(readFileSync(file, "utf-8"));
}

describe("execution adapter", () => {
  it("produces a deterministic trace", async () => {
    const spec = await loadSpec(specPath);
    const trace = executeSpec(spec);
    const expected = readJson(tracePath);
    expect(trace).toEqual(expected);
  });

  it("supports custom prefixes", async () => {
    const spec = await loadSpec(specPath);
    const trace = executeSpec(spec, { vmPrefix: "vmx", networkPrefix: "netx" });
    expect(trace.summary.vms[0]).toMatchObject({ id: "vmx-1" });
    expect(trace.summary.networks[0]).toMatchObject({ id: "netx-1" });
  });

  it("writes canonical artifacts", async () => {
    const dir = mkdtempSync(path.join(tmpdir(), "adapter-ts-"));
    try {
      await writeTraceArtifacts({ outDir: dir, specPath });
      const output = path.join(dir, "adapter-ts-trace.json");
      const trace = readJson(output);
      expect(trace).toEqual(readJson(tracePath));
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });

  it("errors on unknown operations", async () => {
    const spec = await loadSpec(specPath);
    const bad = { ...spec, steps: [...spec.steps, { op: "noop", params: {} }] };
    expect(() => executeSpec(bad)).toThrow(/E_ADAPTER_UNKNOWN_OP/);
  });
});
