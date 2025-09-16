import { mkdtempSync, rmSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";

import { describe, expect, it } from "vitest";

import {
  canonicalJson,
  computeCoverage,
  generateCoverageArtifacts,
} from "../src/index.js";

const SAMPLE_TAGS = [
  {
    spec: "demo-plan",
    version: "0.1",
    stepIndex: 0,
    op: "copy",
    tag: "resource.copy",
    metadata: { src: "bucket-a", dest: "bucket-b" },
  },
  {
    spec: "demo-plan",
    version: "0.1",
    stepIndex: 1,
    op: "create_vm",
    tag: "resource.vm",
    metadata: { id: "vm-1", image: "ubuntu-22.04", cpus: 2 },
  },
  {
    spec: "demo-plan",
    version: "0.1",
    stepIndex: 2,
    op: "create_network",
    tag: "resource.network",
    metadata: { id: "net-1", cidr: "10.0.0.0/24" },
  },
] as const;

describe("coverage generator", () => {
  it("summarises tags deterministically", () => {
    const report = computeCoverage([...SAMPLE_TAGS]);
    expect(report.totals.tags).toBe(3);
    expect(report.byTag["resource.vm"].count).toBe(1);
    expect(report.specs["demo-plan"].coveredOps).toEqual([
      "copy",
      "create_network",
      "create_vm",
    ]);
  });

  it("writes canonical artifacts", async () => {
    const dir = mkdtempSync(path.join(tmpdir(), "coverage-"));
    try {
      const tagFile = path.join(dir, "tags.json");
      writeFileSync(tagFile, canonicalJson(SAMPLE_TAGS));
      await generateCoverageArtifacts({ tagPath: tagFile, outDir: dir });
      const report = readFileSync(path.join(dir, "coverage.json"), "utf-8");
      expect(report.endsWith("\n")).toBe(true);
      const html = readFileSync(path.join(dir, "coverage.html"), "utf-8");
      expect(html.includes("TF Coverage")).toBe(true);
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });
});
