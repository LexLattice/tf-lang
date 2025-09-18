import { execFile as execFileCallback } from "node:child_process";
import { createHash } from "node:crypto";
import { mkdir, readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { promisify } from "node:util";

import { canonicalJson, findRepoRoot } from "@tf-lang/utils";
import { createOracleCtx } from "@tf/oracles-core";
import {
  checkIdempotence,
  type IdempotenceInput,
  type IdempotenceReport,
} from "@tf/oracles-idempotence";

interface SeedPlan {
  readonly seed: string;
  readonly now: number;
}

interface NamedReport {
  readonly name: string;
  readonly report: IdempotenceReport;
  readonly path: string;
  readonly sha256: string;
}

async function main(): Promise<void> {
  try {
    await run();
  } catch (error) {
    console.error(error);
    process.exitCode = 1;
  }
}

async function run(): Promise<void> {
  const repoRoot = findRepoRoot();
  const outDir = path.join(repoRoot, "out", "t3");
  await mkdir(outDir, { recursive: true });

  const seeds: SeedPlan[] = [{ seed: "0xidempotence0001", now: 0 }];
  const reports: NamedReport[] = [];
  const seedsLog: string[] = [];

  for (const plan of seeds) {
    const ctx = createOracleCtx(plan.seed, { now: plan.now });
    const input = createIdempotenceInput(plan.seed);
    const result = await checkIdempotence(input, ctx);
    const report = materializeReport(result, input);
    const targetPath = path.join(outDir, "idempotence", "report.json");
    await writeReport(targetPath, report);
    const sha256 = await writeSha256(targetPath);
    reports.push({ name: "idempotence", report, path: targetPath, sha256 });

    for (const item of input.cases ?? []) {
      seedsLog.push(
        JSON.stringify({
          seed: plan.seed,
          now: plan.now,
          case: `idempotence:${item.name}`,
          runtime: "ts",
        }),
      );
    }
  }

  const seedsPath = path.join(outDir, "harness-seeds.jsonl");
  await writeFile(seedsPath, `${seedsLog.join("\n")}\n`, "utf8");

  await writeRollup(outDir, reports);
  await writeCertificate(repoRoot, outDir, reports);
}

function createIdempotenceInput(seed: string): IdempotenceInput {
  const values = deriveValues(seed);
  return {
    cases: [
      {
        name: `numbers-${seed.slice(-4)}`,
        once: values,
        twice: values,
      },
    ],
  };
}

function deriveValues(seed: string): number[] {
  const hex = seed.replace(/[^0-9a-f]/gi, "").toLowerCase();
  const result: number[] = [];
  for (let index = 0; index < hex.length; index += 2) {
    const chunk = hex.slice(index, index + 2);
    if (chunk.length === 0) {
      break;
    }
    result.push(Number.parseInt(chunk, 16) % 10);
    if (result.length >= 5) {
      break;
    }
  }
  if (result.length === 0) {
    return [0, 1, 2];
  }
  return result;
}

function materializeReport(
  result: Awaited<ReturnType<typeof checkIdempotence>>,
  input: IdempotenceInput,
): IdempotenceReport {
  if (result.ok) {
    return result.value;
  }
  const report = (result.error.details as { report?: IdempotenceReport } | undefined)?.report;
  if (report) {
    return report;
  }
  const total = input.cases?.length ?? 0;
  const failed = total > 0 ? 1 : 0;
  return {
    total,
    passed: total - failed,
    failed,
  };
}

async function writeReport(targetPath: string, report: IdempotenceReport): Promise<void> {
  await mkdir(path.dirname(targetPath), { recursive: true });
  await writeFile(targetPath, canonicalJson(report), "utf8");
}

async function writeSha256(targetPath: string): Promise<string> {
  const content = await readFile(targetPath);
  const hash = createHash("sha256").update(content).digest("hex");
  await writeFile(`${targetPath}.sha256`, `${hash}\n`, "utf8");
  return hash;
}

async function writeRollup(outDir: string, reports: NamedReport[]): Promise<void> {
  const entries: Record<string, IdempotenceReport> = {};
  for (const item of reports) {
    entries[item.name] = item.report;
  }
  const summary = reports.reduce(
    (acc, item) => {
      return {
        total: acc.total + item.report.total,
        passed: acc.passed + item.report.passed,
        failed: acc.failed + item.report.failed,
      };
    },
    { total: 0, passed: 0, failed: 0 },
  );
  const rollupPath = path.join(outDir, "oracles-report.json");
  await writeFile(
    rollupPath,
    canonicalJson({ reports: entries, summary }),
    "utf8",
  );
}

async function writeCertificate(
  repoRoot: string,
  outDir: string,
  reports: NamedReport[],
): Promise<void> {
  const execFile = promisify(execFileCallback);
  const commit = (await execFile("git", ["rev-parse", "HEAD"], { cwd: repoRoot }))
    .stdout.trim();
  const certificate = {
    commit,
    reports: reports.map((item) => ({
      name: item.name,
      path: path.relative(repoRoot, item.path),
      sha256: item.sha256,
    })),
  };
  const certificatePath = path.join(outDir, "certificate.json");
  await writeFile(certificatePath, canonicalJson(certificate), "utf8");
  const content = await readFile(certificatePath);
  const hash = createHash("sha256").update(content).digest("hex");
  await writeFile(`${certificatePath}.sha256`, `${hash}\n`, "utf8");
}

void main();
