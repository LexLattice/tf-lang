import { existsSync } from "node:fs";
import { mkdir, writeFile, readFile } from "node:fs/promises";
import path from "node:path";
import { execFile } from "node:child_process";
import { promisify } from "node:util";
import { describe, expect, it } from "vitest";
import { canonicalJson, withTmpDir } from "@tf-lang/utils";
import {
  applyScaffoldPlan,
  formatPlanSummary,
  generateScaffoldPlan,
  readScaffoldPlan,
  writeScaffoldPlan,
} from "../src/index.js";

const execFileAsync = promisify(execFile);

async function writeTemplateFixture(root: string): Promise<void> {
  const templateRoot = path.join(root, "templates", "t4", "test");
  await mkdir(path.join(templateRoot, "workdir"), { recursive: true });
  await mkdir(path.join(templateRoot, "ci"), { recursive: true });
  await writeFile(
    path.join(templateRoot, "template.json"),
    canonicalJson({
      name: "test",
      description: "Test template",
      workdir: {
        files: [
          { source: "workdir/README.md", target: "README.md" },
        ],
      },
      ci: {
        reusableWorkflow: {
          source: "ci/reusable.yml",
          target: ".github/workflows/reusable.yml",
        },
        branchWorkflows: [
          {
            source: "ci/branch.yml",
            target: ".github/workflows/{{branchSlug}}.yml",
          },
        ],
      },
      packageJson: {
        scripts: {
          "tf:check": "pnpm --filter @tf-lang/tf-check run artifacts",
        },
      },
    })
  );
  await writeFile(path.join(templateRoot, "workdir", "README.md"), "# {{branchName}}\n");
  await writeFile(path.join(templateRoot, "ci", "reusable.yml"), "name: reusable\n");
  await writeFile(
    path.join(templateRoot, "ci", "branch.yml"),
    "name: branch {{branchName}}\n"
  );
}

async function writePlanFixture(root: string): Promise<{ ndjson: string; json: string }> {
  const planDir = path.join(root, "out", "t4", "plan");
  await mkdir(planDir, { recursive: true });
  const nodes = [
    {
      nodeId: "node-a",
      specId: "demo",
      component: "plan",
      choice: "runtime=node|database=postgres",
      deps: [],
      rationale: "Option A",
      score: {
        total: 5,
        complexity: 2,
        risk: 1,
        perf: 2,
        devTime: 1,
        depsReady: 1,
        explain: [],
      },
    },
    {
      nodeId: "node-b",
      specId: "demo",
      component: "plan",
      choice: "runtime=rust|database=sqlite",
      deps: [],
      rationale: "Option B",
      score: {
        total: 4,
        complexity: 2,
        risk: 1.5,
        perf: 1,
        devTime: 1,
        depsReady: 1,
        explain: [],
      },
    },
  ];
  const graph = {
    nodes,
    edges: [],
    meta: {
      specId: "demo",
      specHash: "hash-demo",
      seed: 42,
      version: "0.1.0",
    },
  };
  const jsonPath = path.join(planDir, "plan.json");
  const ndjsonPath = path.join(planDir, "plan.ndjson");
  await writeFile(jsonPath, canonicalJson(graph));
  await writeFile(ndjsonPath, `${nodes.map((node) => JSON.stringify(node)).join("\n")}\n`);
  return { ndjson: ndjsonPath, json: jsonPath };
}

describe("tf-plan-scaffold", () => {
  it("generates and reads scaffold plans", async () => {
    await withTmpDir("scaffold-", async (dir) => {
      await writeTemplateFixture(dir);
      const planPaths = await writePlanFixture(dir);
      const plan = await generateScaffoldPlan({
        planPath: planPaths.ndjson,
        templateName: "test",
        planOptions: { metaPath: planPaths.json },
        templateOptions: { repoRoot: dir },
        limit: 1,
      });
      expect(plan.branches).toHaveLength(1);
      const summary = formatPlanSummary(plan);
      expect(summary).toContain("demo");
      const outPath = path.join(dir, "out", "t4", "scaffold", "index.json");
      await writeScaffoldPlan(plan, outPath);
      const loaded = await readScaffoldPlan(outPath);
      expect(loaded).toEqual(plan);
    });
  });

  it("applies scaffold plans into a git repository", async () => {
    await withTmpDir("scaffold-apply-", async (dir) => {
      await writeTemplateFixture(dir);
      const planPaths = await writePlanFixture(dir);
      const plan = await generateScaffoldPlan({
        planPath: planPaths.ndjson,
        templateName: "test",
        planOptions: { metaPath: planPaths.json },
        templateOptions: { repoRoot: dir },
        limit: 1,
      });
      const repoRoot = path.join(dir, "repo");
      await mkdir(repoRoot, { recursive: true });
      await writeFile(path.join(repoRoot, "package.json"), canonicalJson({ name: "fixture", version: "0.0.0" }));
      await execFileAsync("git", ["init", "--initial-branch=main"], { cwd: repoRoot });
      await execFileAsync("git", ["config", "user.email", "ci@example.com"], { cwd: repoRoot });
      await execFileAsync("git", ["config", "user.name", "CI"], { cwd: repoRoot });
      await writeFile(path.join(repoRoot, "README.md"), "initial\n");
      await execFileAsync("git", ["add", "."], { cwd: repoRoot });
      await execFileAsync("git", ["commit", "-m", "init"], { cwd: repoRoot });

      await applyScaffoldPlan(plan, { repoRoot, stdio: "ignore" });

      const branchWorkdir = plan.branches[0]?.worktreePath ?? "";
      const branchReadme = path.join(repoRoot, branchWorkdir, "README.md");
      expect(existsSync(branchReadme)).toBe(true);
      const pkg = JSON.parse(await readFile(path.join(repoRoot, "package.json"), "utf-8")) as {
        scripts?: Record<string, string>;
      };
      expect(pkg.scripts?.["tf:check"]).toBe("pnpm --filter @tf-lang/tf-check run artifacts");
    });
  });
});
