import { describe, expect, it } from "vitest";
import { createScaffoldPlan } from "../src/index.js";
import type { PlanSource, TemplateFileTemplate, TemplatePack } from "../src/index.js";

const SAMPLE_TEMPLATE_FILES: TemplateFileTemplate[] = [
  {
    scope: "global",
    target: "repo",
    sourcePath: "repo/readme.md",
    relativePathTemplate: "docs/{{specId}}-overview.md",
    contentTemplate: "# Overview for {{specId}}\n",
  },
  {
    scope: "branch",
    target: "workdir",
    sourcePath: "workdir/readme.md",
    relativePathTemplate: "README.md",
    contentTemplate: "# Branch {{branchName}}\nPlan node {{nodeId}}\n",
  },
  {
    scope: "branch",
    target: "ci",
    sourcePath: "ci/workflow.yml",
    relativePathTemplate: ".github/workflows/{{branchSlug}}.yml",
    contentTemplate: "name: Branch {{branchName}}\n",
  },
];

const SAMPLE_TEMPLATE: TemplatePack = {
  name: "dual-stack",
  description: "Sample template for tests",
  files: SAMPLE_TEMPLATE_FILES,
  packageJsonScripts: {
    "tf:check": "pnpm --filter @tf-lang/tf-check run artifacts",
  },
};

const SAMPLE_SOURCE: PlanSource = {
  meta: {
    specId: "demo",
    specHash: "abc123",
    seed: 42,
    version: "0.1.0",
  },
  nodes: [
    {
      nodeId: "node-1",
      specId: "demo",
      component: "plan",
      choice: "runtime=node|database=postgres",
      deps: [],
      rationale: "First plan",
      score: {
        total: 10,
        complexity: 5,
        risk: 2,
        perf: 3,
        devTime: 1,
        depsReady: 4,
        explain: ["sample"],
      },
    },
    {
      nodeId: "node-2",
      specId: "demo",
      component: "plan",
      choice: "runtime=rust|database=sqlite",
      deps: [],
      rationale: "Second plan",
      score: {
        total: 8,
        complexity: 4,
        risk: 3,
        perf: 2,
        devTime: 2,
        depsReady: 3,
        explain: ["sample"],
      },
    },
  ],
};

describe("createScaffoldPlan", () => {
  it("selects the highest scoring plan and renders files", () => {
    const plan = createScaffoldPlan(SAMPLE_SOURCE, { template: SAMPLE_TEMPLATE, limit: 1 });
    expect(plan.branches).toHaveLength(1);
    const branch = plan.branches[0];
    expect(branch.repoActions).toEqual([
      {
        type: "create-branch",
        branchName: expect.stringContaining("plan/demo"),
        baseBranch: "main",
      },
    ]);
    expect(branch.files).toHaveLength(2);
    expect(branch.files[0]).toMatchObject({
      target: "workdir",
      path: "README.md",
    });
    expect(plan.global.files).toHaveLength(1);
    expect(plan.global.files[0].path).toBe("docs/demo-overview.md");
    expect(plan.global.packageJsonUpdates[0]?.scripts).toHaveProperty(
      "tf:check",
      "pnpm --filter @tf-lang/tf-check run artifacts"
    );
  });

  it("is deterministic for the same input", () => {
    const first = createScaffoldPlan(SAMPLE_SOURCE, { template: SAMPLE_TEMPLATE, limit: 2 });
    const second = createScaffoldPlan(SAMPLE_SOURCE, { template: SAMPLE_TEMPLATE, limit: 2 });
    expect(second).toEqual(first);
  });

  it("enforces selection limit but always returns at least one branch", () => {
    const plan = createScaffoldPlan(SAMPLE_SOURCE, { template: SAMPLE_TEMPLATE, limit: 0 });
    expect(plan.branches.length).toBe(1);
    expect(plan.meta.selectedBranches).toBe(1);
  });
});
