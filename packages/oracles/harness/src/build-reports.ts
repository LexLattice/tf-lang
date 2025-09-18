import { createHash } from "node:crypto";
import { execFile } from "node:child_process";
import { mkdir, readFile, readdir, writeFile } from "node:fs/promises";
import path from "node:path";
import { performance } from "node:perf_hooks";
import { promisify } from "node:util";

import { createOracleCtx } from "@tf/oracles-core";
import { checkIdempotence } from "@tf/oracles-idempotence";
import type { IdempotenceInput } from "@tf/oracles-idempotence";
import { findRepoRoot } from "@tf-lang/utils";

const execFileAsync = promisify(execFile);

interface HarnessSeedEntry {
  readonly seed: string;
  readonly now: string;
  readonly case: string;
  readonly runtime: number;
}

interface OracleReportSummary {
  readonly total: number;
  readonly passed: number;
  readonly failed: number;
  readonly firstFail?: {
    readonly pointer: string;
    readonly once: unknown;
    readonly twice: unknown;
  };
}

async function main(): Promise<void> {
  const repoRoot = findRepoRoot();
  const outDir = path.join(repoRoot, "out", "t3");
  const idempotenceOutDir = path.join(outDir, "idempotence");
  await mkdir(idempotenceOutDir, { recursive: true });

  const start = performance.now();
  const idempotenceReport = await runIdempotence(repoRoot);
  const seedEntry: HarnessSeedEntry = {
    seed: "0x5eed-idem-0001",
    now: new Date().toISOString(),
    case: "idempotence-fixtures",
    runtime: Number((performance.now() - start).toFixed(3)),
  };

  const seedsPath = path.join(outDir, "harness-seeds.jsonl");
  await writeFile(seedsPath, `${JSON.stringify(seedEntry)}\n`, { encoding: "utf-8" });

  const idempotenceReportPath = path.join(idempotenceOutDir, "report.json");
  await writeJson(idempotenceReportPath, idempotenceReport);
  await writeSha256(idempotenceReportPath);

  const gitCommit = await resolveGitCommit(repoRoot);
  const generated = new Date().toISOString();

  const rollupPath = path.join(outDir, "oracles-report.json");
  const rollup = {
    summary: { generated, git: gitCommit },
    oracles: { idempotence: idempotenceReport },
    seeds: { total: 1, entries: [seedEntry] },
  };
  await writeJson(rollupPath, rollup);
  await writeSha256(rollupPath);

  const certificatePath = path.join(outDir, "certificate.json");
  const certificate = {
    generated,
    git: gitCommit,
    reports: [
      { path: relativePath(repoRoot, idempotenceReportPath), sha256: await readSha(idempotenceReportPath) },
      { path: relativePath(repoRoot, rollupPath), sha256: await readSha(rollupPath) },
    ],
  };
  await writeJson(certificatePath, certificate);
}

async function runIdempotence(repoRoot: string): Promise<OracleReportSummary> {
  const fixturesDir = path.join(repoRoot, "packages", "oracles", "idempotence", "fixtures");
  const entries = (await readdir(fixturesDir)).filter((file) => file.endsWith(".json")).sort();
  const ctx = createOracleCtx("0xfeed", { now: 0 });

  let passed = 0;
  let failed = 0;
  let firstFail: OracleReportSummary["firstFail"] = undefined;

  for (const file of entries) {
    const payload = JSON.parse(await readFile(path.join(fixturesDir, file), "utf-8")) as {
      readonly input: IdempotenceInput;
    };
    const result = await checkIdempotence(payload.input, ctx);
    if (result.ok) {
      passed += 1;
      continue;
    }

    failed += 1;
    if (!firstFail) {
      const details = result.error.details as { mismatches?: ReadonlyArray<{ pointer: string; once: unknown; twice: unknown }> } | undefined;
      const first = details?.mismatches?.[0];
      if (first) {
        firstFail = { pointer: first.pointer, once: first.once, twice: first.twice };
      }
    }
  }

  return { total: entries.length, passed, failed, ...(firstFail ? { firstFail } : {}) };
}

async function writeJson(filePath: string, data: unknown): Promise<void> {
  await mkdir(path.dirname(filePath), { recursive: true });
  await writeFile(filePath, `${JSON.stringify(data, null, 2)}\n`, { encoding: "utf-8" });
}

async function writeSha256(filePath: string): Promise<void> {
  const hash = await readSha(filePath);
  await writeFile(`${filePath}.sha256`, `${hash}\n`, { encoding: "utf-8" });
}

async function readSha(filePath: string): Promise<string> {
  const buffer = await readFile(filePath);
  return createHash("sha256").update(buffer).digest("hex");
}

async function resolveGitCommit(repoRoot: string): Promise<string> {
  try {
    const { stdout } = await execFileAsync("git", ["rev-parse", "HEAD"], { cwd: repoRoot });
    return stdout.trim();
  } catch (error) {
    return "unknown";
  }
}

function relativePath(root: string, target: string): string {
  return path.relative(root, target) || path.basename(target);
}

void main();

export {
  runIdempotence,
  writeJson,
  writeSha256,
  readSha,
  relativePath,
};

export type { OracleReportSummary };
