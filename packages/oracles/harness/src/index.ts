import { createHash } from "node:crypto";
import { execFile } from "node:child_process";
import { promisify } from "node:util";
import { readFile, writeFile, mkdir } from "node:fs/promises";
import { dirname, join, relative } from "node:path";

import { canonicalJson, findRepoRoot } from "@tf-lang/utils";
import { createOracleCtx, pointerFromSegments } from "@tf/oracles-core";
import { checkConservation } from "@tf/oracles-conservation";
import type { ConservationInput, ConservationViolation } from "@tf/oracles-conservation";
import { checkIdempotence } from "@tf/oracles-idempotence";
import type { IdempotenceInput, IdempotenceMismatch } from "@tf/oracles-idempotence";
import { checkTransport } from "@tf/oracles-transport";
import type { TransportInput, TransportMismatch } from "@tf/oracles-transport";

const HARNESS_SEEDS = ["0x00000001", "0x00000002", "0x00000003"] as const;
const CONTEXT_SEED = "0xfeed";
const CONTEXT_NOW = 0;
const CASE_IDEMPOTENCE = "idempotence.basic";
const CASE_CONSERVATION = "conservation.basic";
const execFileAsync = promisify(execFile);
const CASE_TRANSPORT = "transport.basic";

interface OracleReport {
  total: number;
  passed: number;
  failed: number;
  firstFail?: {
    pointer: string;
    left: unknown;
    right: unknown;
  };
}

async function main(): Promise<void> {
  const repoRoot = findRepoRoot();
  const outDir = join(repoRoot, "out", "t3");
  await mkdir(outDir, { recursive: true });

  const idempotenceReport: OracleReport = { total: 0, passed: 0, failed: 0 };
  const conservationReport: OracleReport = { total: 0, passed: 0, failed: 0 };
  const transportReport: OracleReport = { total: 0, passed: 0, failed: 0 };
  const seedsLogLines: string[] = [];

  for (const seed of HARNESS_SEEDS) {
    const ctx = createOracleCtx(CONTEXT_SEED, { now: CONTEXT_NOW });

    const idempotenceInput = buildIdempotenceInput(seed);
    const idempotenceResult = await checkIdempotence(idempotenceInput, ctx);

    idempotenceReport.total += 1;
    if (idempotenceResult.ok) {
      idempotenceReport.passed += 1;
    } else {
      idempotenceReport.failed += 1;
      const mismatch = firstMismatch(idempotenceResult.error.details);
      if (mismatch && !idempotenceReport.firstFail) {
        idempotenceReport.firstFail = mismatch;
      }
    }

    seedsLogLines.push(
      JSON.stringify({
        seed,
        case: CASE_IDEMPOTENCE,
        now: CONTEXT_NOW,
        status: idempotenceResult.ok ? "pass" : "fail",
      }),
    );

    const conservationInput = buildConservationInput(seed);
    const conservationResult = await checkConservation(conservationInput, ctx);

    conservationReport.total += 1;
    if (conservationResult.ok) {
      conservationReport.passed += 1;
    } else {
      conservationReport.failed += 1;
      const violation = firstConservationViolation(conservationResult.error.details);
      if (violation && !conservationReport.firstFail) {
        conservationReport.firstFail = violation;
      }
    }

    seedsLogLines.push(
      JSON.stringify({
        seed,
        case: CASE_CONSERVATION,
        now: CONTEXT_NOW,
        status: conservationResult.ok ? "pass" : "fail",
      }),
    );

    const transportInput = buildTransportInput(seed);
    const transportResult = await checkTransport(transportInput, ctx);

    transportReport.total += 1;
    if (transportResult.ok) {
      transportReport.passed += 1;
    } else {
      transportReport.failed += 1;
      const mismatch = firstTransportMismatch(transportResult.error.details);
      if (mismatch && !transportReport.firstFail) {
        transportReport.firstFail = mismatch;
      }
    }

    seedsLogLines.push(
      JSON.stringify({
        seed,
        case: CASE_TRANSPORT,
        now: CONTEXT_NOW,
        status: transportResult.ok ? "pass" : "fail",
      }),
    );
  }

  await writeSeedsLog(join(outDir, "harness-seeds.jsonl"), seedsLogLines);

  const idempotenceReportPath = join(outDir, "idempotence", "report.json");
  await ensureDir(idempotenceReportPath);
  await writeFile(idempotenceReportPath, canonicalJson(idempotenceReport), "utf-8");

  const conservationReportPath = join(outDir, "conservation", "report.json");
  await ensureDir(conservationReportPath);
  await writeFile(conservationReportPath, canonicalJson(conservationReport), "utf-8");

  const transportReportPath = join(outDir, "transport", "report.json");
  await ensureDir(transportReportPath);
  await writeFile(transportReportPath, canonicalJson(transportReport), "utf-8");

  const oraclesReportPath = join(outDir, "oracles-report.json");
  const rollup = { idempotence: idempotenceReport, conservation: conservationReport, transport: transportReport };
  await writeFile(oraclesReportPath, canonicalJson(rollup), "utf-8");

  const certificatePath = join(outDir, "certificate.json");
  const artifacts = await recordArtifacts(repoRoot, [
    idempotenceReportPath,
    conservationReportPath,
    transportReportPath,
    oraclesReportPath,
  ]);
  const commit = await gitRevParse(repoRoot);
  const certificate = {
    commit,
    generatedAt: CONTEXT_NOW,
    artifacts: artifacts.map(({ path, sha256 }) => ({ path, sha256 })),
  };
  await writeFile(certificatePath, canonicalJson(certificate), "utf-8");
  const certificateHash = createHash("sha256").update(await readFile(certificatePath)).digest("hex");
  await writeFile(`${certificatePath}.sha256`, `${certificateHash}\n`, "utf-8");
}

function buildIdempotenceInput(seed: string): IdempotenceInput {
  const vector = deriveVector(seed);
  return {
    cases: [
      {
        name: `seed:${seed}`,
        seed,
        applications: [
          { iteration: 0, value: { vector } },
          { iteration: 1, value: { vector } },
        ],
      },
    ],
  };
}

function buildConservationInput(seed: string): ConservationInput {
  const [records, warnings, alerts] = deriveVector(seed);
  return {
    keys: ["records", "warnings", "alerts"],
    before: { records, warnings, alerts },
    after: { records, warnings, alerts },
  };
}

function buildTransportInput(seed: string): TransportInput {
  const vector = deriveVector(seed);
  return {
    value: {
      seed,
      vector,
      checksum: vector.reduce((sum, entry) => sum + entry, 0),
    },
  };
}

function deriveVector(seed: string): number[] {
  const parsed = Number.parseInt(seed, 16);
  const a = parsed & 0xff;
  const b = (parsed >> 8) & 0xff;
  const c = (parsed >> 16) & 0xff;
  return [a % 97, b % 97, c % 97];
}

function firstMismatch(details: unknown): OracleReport["firstFail"] | undefined {
  if (!details || typeof details !== "object") {
    return undefined;
  }
  const payload = details as { mismatches?: ReadonlyArray<IdempotenceMismatch> };
  const mismatch = payload.mismatches?.[0];
  if (!mismatch) {
    return undefined;
  }
  return {
    pointer: mismatch.pointer,
    left: mismatch.expected,
    right: mismatch.actual,
  };
}

function firstConservationViolation(details: unknown): OracleReport["firstFail"] | undefined {
  if (!details || typeof details !== "object") {
    return undefined;
  }
  const payload = details as { violations?: ReadonlyArray<ConservationViolation> };
  const violation = payload.violations?.[0];
  if (!violation) {
    return undefined;
  }
  return {
    pointer: pointerFromSegments([violation.key]),
    left: violation.before,
    right: violation.after,
  };
}

function firstTransportMismatch(details: unknown): OracleReport["firstFail"] | undefined {
  if (!details || typeof details !== "object") {
    return undefined;
  }
  const payload = details as { mismatches?: ReadonlyArray<TransportMismatch> };
  const mismatch = payload.mismatches?.[0];
  if (!mismatch) {
    return undefined;
  }
  return {
    pointer: mismatch.pointer,
    left: mismatch.expected,
    right: mismatch.actual,
  };
}

async function recordArtifacts(
  repoRoot: string,
  paths: ReadonlyArray<string>,
): Promise<ReadonlyArray<{ path: string; sha256: string }>> {
  const results: Array<{ path: string; sha256: string }> = [];
  for (const filePath of paths) {
    const relativePath = relative(repoRoot, filePath);
    const data = await readFile(filePath);
    const hash = createHash("sha256").update(data).digest("hex");
    await writeFile(`${filePath}.sha256`, `${hash}\n`, "utf-8");
    results.push({ path: relativePath.replace(/\\/g, "/"), sha256: hash });
  }
  return results;
}

async function gitRevParse(repoRoot: string): Promise<string> {
  const { stdout } = await execFileAsync("git", ["rev-parse", "HEAD"], { cwd: repoRoot });
  return stdout.trim();
}

async function ensureDir(filePath: string): Promise<void> {
  await mkdir(dirname(filePath), { recursive: true });
}

async function writeSeedsLog(path: string, lines: ReadonlyArray<string>): Promise<void> {
  const content = lines.length > 0 ? `${lines.join("\n")}\n` : "";
  await writeFile(path, content, "utf-8");
}

main().catch((error) => {
  console.error(error);
  process.exitCode = 1;
});
