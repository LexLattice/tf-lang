import { existsSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { writeFile } from "node:fs/promises";

import { describe, expect, it } from "vitest";

import {
  canonicalJson,
  canonicalize,
  escapeHtml,
  findRepoRoot,
  withTmpDir,
} from "../src/index.js";

describe("@tf-lang/utils", () => {
  it("canonicalizes objects deterministically", () => {
    const input = { b: 1, a: { z: 2, y: [3, 1] }, c: null };
    const canonical = canonicalize(input) as Record<string, unknown>;
    expect(Object.keys(canonical)).toEqual(["a", "b", "c"]);
    expect(canonicalJson(input)).toContain("\n");
  });

  it("escapes HTML entities", () => {
    expect(escapeHtml("<script>&")).toBe("&lt;script&gt;&amp;");
  });

  it("finds the repository root containing pnpm-workspace.yaml", () => {
    const here = path.dirname(fileURLToPath(import.meta.url));
    const root = findRepoRoot(here);
    expect(existsSync(path.join(root, "pnpm-workspace.yaml"))).toBe(true);
  });

  it("creates and cleans temporary directories", async () => {
    let tempDir = "";
    await withTmpDir("inner-", async (dir) => {
      tempDir = dir;
      expect(dir.startsWith(tmpdir())).toBe(true);
      const marker = path.join(dir, "touch.txt");
      await writeFile(marker, "ok", "utf-8");
      expect(existsSync(marker)).toBe(true);
    });
    expect(tempDir).not.toBe("");
    expect(existsSync(tempDir)).toBe(false);
  });
});
