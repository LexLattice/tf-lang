import { existsSync } from "node:fs";
import path from "node:path";

import { describe, expect, it } from "vitest";

import {
  canonicalJson,
  escapeHtml,
  findRepoRoot,
  withTmpDir,
} from "../src/index.js";

describe("@tf-lang/utils", () => {
  it("produces canonical JSON with sorted keys", () => {
    const json = canonicalJson({ b: 2, a: 1 });
    expect(json).toBe(`{\n  "a": 1,\n  "b": 2\n}\n`);
  });

  it("escapes HTML-reserved characters", () => {
    expect(escapeHtml('<script>&"\'')).toBe("&lt;script&gt;&amp;&quot;&#39;");
  });

  it("cleans up temporary directories", async () => {
    let tmpPath = "";
    await withTmpDir("utils-test-", async (dir) => {
      tmpPath = dir;
      expect(existsSync(dir)).toBe(true);
    });
    expect(tmpPath).not.toBe("");
    expect(existsSync(tmpPath)).toBe(false);
  });

  it("finds the repository root from nested directories", () => {
    const start = new URL(".", import.meta.url).pathname;
    const repoRoot = findRepoRoot(start);
    expect(path.basename(repoRoot)).toBe("tf-lang");
  });
});
