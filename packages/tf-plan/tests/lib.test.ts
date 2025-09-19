import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { enumeratePlan, summarizePlan, writePlanNdjson } from "../src/index.js";

function fixture(name: string): string {
  return fileURLToPath(new URL(`../../../tests/specs/${name}`, import.meta.url));
}

describe("tf-plan library", () => {
  it("enumerates and summarizes a plan", async () => {
    const specPath = fixture("demo.json");
    const graph = await enumeratePlan({ specPath, seed: 42, beamWidth: 6 });
    const summary = summarizePlan(graph, 3);
    expect(summary.nodes.length).toBeGreaterThan(0);
    expect(summary.specId).toBe("demo");
  });

  it("writes ndjson deterministically", async () => {
    const specPath = fixture("minimal.json");
    const graph = await enumeratePlan({ specPath, seed: 1 });
    const tmp = path.join(process.cwd(), "out", "t4", "plan", "test.ndjson");
    await writePlanNdjson(graph, tmp, (node) => node.component === "plan");
    const contents = readFileSync(tmp, "utf-8");
    const lines = contents.trim().split("\n");
    expect(lines.length).toBeGreaterThan(0);
    const parsed = lines.map((line) => JSON.parse(line));
    expect(parsed.every((item) => item.component === "plan")).toBe(true);
  });
});
