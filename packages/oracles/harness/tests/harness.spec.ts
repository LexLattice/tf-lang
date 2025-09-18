import { mkdtemp } from "node:fs/promises";
import { readFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";

import { describe, expect, it } from "vitest";

import { findRepoRoot } from "@tf-lang/utils";

import {
  readSha,
  relativePath,
  runIdempotence,
  writeJson,
  writeSha256,
} from "../src/build-reports.js";

const createTempDir = () => mkdtemp(path.join(tmpdir(), "harness-spec-"));

describe("build-reports helpers", () => {
  it("writes canonical JSON with a trailing newline", async () => {
    const dir = await createTempDir();
    const filePath = path.join(dir, "report.json");
    await writeJson(filePath, { alpha: 1, beta: [2, 3] });
    const contents = await readFile(filePath, "utf-8");
    expect(contents.endsWith("\n")).toBe(true);
    expect(JSON.parse(contents)).toEqual({ alpha: 1, beta: [2, 3] });
  });

  it("writes deterministic SHA256 sidecars", async () => {
    const dir = await createTempDir();
    const filePath = path.join(dir, "payload.json");
    await writeJson(filePath, { foo: "bar" });
    await writeSha256(filePath);
    const digestPayload = await readFile(`${filePath}.sha256`, "utf-8");
    expect(digestPayload.endsWith("\n")).toBe(true);
    const digest = digestPayload.trim();
    expect(digest).toMatch(/^[0-9a-f]{64}$/);
    await expect(readSha(filePath)).resolves.toBe(digest);
  });

  it("computes stable relative paths", () => {
    const repoRoot = "/repo";
    expect(relativePath(repoRoot, "/repo/out/t3/report.json")).toBe("out/t3/report.json");
    expect(relativePath(repoRoot, "/repo")).toBe("repo");
  });
});

describe("runIdempotence", () => {
  it("summarizes the checked fixtures", async () => {
    const summary = await runIdempotence(findRepoRoot());
    expect(summary).toMatchObject({
      total: 2,
      passed: 1,
      failed: 1,
      firstFail: { pointer: "/data/3" },
    });
    expect(summary.total).toBe(summary.passed + summary.failed);
  });
});
