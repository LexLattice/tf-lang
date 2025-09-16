import { existsSync } from "node:fs";
import { writeFile } from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";

import { describe, expect, it } from "vitest";

import {
  canonicalJson,
  escapeHtml,
  findRepoRoot,
  withTmpDir,
} from "../src/index.js";

const here = path.dirname(fileURLToPath(import.meta.url));

describe("@tf-lang/utils", () => {
  it("canonicalizes objects with sorted keys", () => {
    const json = canonicalJson({ b: 1, a: [2, 1] });
    expect(json.endsWith("\n")).toBe(true);
    const parsed = JSON.parse(json) as { a: number[]; b: number };
    expect(parsed).toEqual({ a: [2, 1], b: 1 });
    expect(json.indexOf('"a"')).toBeLessThan(json.indexOf('"b"'));
  });

  it("finds the repository root from a nested path", () => {
    const repoRoot = findRepoRoot(here);
    expect(path.basename(repoRoot)).toBe("tf-lang");
    expect(existsSync(path.join(repoRoot, "pnpm-workspace.yaml"))).toBe(true);
  });

  it("cleans up temporary directories via withTmpDir", async () => {
    let createdPath = "";
    await withTmpDir("utils-test-", async (dir) => {
      createdPath = dir;
      const file = path.join(dir, "value.txt");
      await writeFile(file, "ok", "utf-8");
      expect(existsSync(file)).toBe(true);
    });
    expect(existsSync(createdPath)).toBe(false);
  });

  it("escapes HTML entities", () => {
    const escaped = escapeHtml("<script>\"&'</script>");
    expect(escaped).toBe("&lt;script&gt;&quot;&amp;&#39;&lt;/script&gt;");
  });
});
