import { createHash } from "node:crypto";
import { execFile } from "node:child_process";
import { promisify } from "node:util";
import { readFile, writeFile, mkdir } from "node:fs/promises";
import { dirname, join, relative } from "node:path";

import { canonicalJson, findRepoRoot } from "@tf-lang/utils";
import { createOracleCtx } from "@tf/oracles-core";
import { checkConservation } from "@tf/oracles-conservation";
import type { ConservationInput, ConservationViolation } from "@tf/oracles-conservation";
import { checkIdempotence } from "@tf/oracles-idempotence";
import type { IdempotenceInput, IdempotenceMismatch } from "@tf/oracles-idempotence";
import { checkTransport } from "@tf/oracles-transport";
import type { TransportDrift, TransportInput } from "@tf/oracles-transport";

const HARNESS_SEEDS = ["0x00000001"] as const;
const CONTEXT_SEED = "0xfeed";
const CONTEXT_NOW = 0;
const CASE_IDEMPOTENCE = "idempotence.basic";
const CASE_CONSERVATION = "conservation.basic";
const CASE_TRANSPORT = "transport.basic";
const execFileAsync = promisify(execFile);

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
    seedsLogLines.push(buildSeedLogLine(seed, CASE_IDEMPOTENCE, idempotenceResult.ok));

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

    seedsLogLines.push(buildSeedLogLine(seed, CASE_CONSERVATION, conservationResult.ok));

    const transportInput = buildTransportInput(seed);
    const transportResult = await checkTransport(transportInput, ctx);

    transportReport.total += 1;
    if (transportResult.ok) {
      transportReport.passed += 1;
    } else {
      transportReport.failed += 1;
      const drift = firstTransportDrift(transportResult.error.details);
      if (drift && !transportReport.firstFail) {
        transportReport.firstFail = drift;
      }
    }

    seedsLogLines.push(buildSeedLogLine(seed, CASE_TRANSPORT, transportResult.ok));
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
  const rollup = {
    idempotence: idempotenceReport,
    conservation: conservationReport,
    transport: transportReport,
  };
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
  await writeSha256(certificatePath);

  await writeParityPlaceholders(join(outDir, "parity"));
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
  const summary = {
    min: Math.min(...vector),
    max: Math.max(...vector),
    checksum: vector.reduce((total, value) => total + value, 0) % 257,
  };
  return {
    cases: [
      {
        name: `seed:${seed}`,
        seed,
        value: {
          seed,
          vector,
          summary,
        },
      },
    ],
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
    pointer: `/${escapePointerSegment(violation.key)}`,
    left: violation.before,
    right: violation.after,
  };
}

function firstTransportDrift(details: unknown): OracleReport["firstFail"] | undefined {
  if (!details || typeof details !== "object") {
    return undefined;
  }
  const payload = details as { drifts?: ReadonlyArray<TransportDrift> };
  const drift = payload.drifts?.[0];
  if (!drift) {
    return undefined;
  }
  return {
    pointer: drift.pointer,
    left: drift.before,
    right: drift.after,
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

async function writeSha256(filePath: string): Promise<void> {
  const data = await readFile(filePath);
  const hash = createHash("sha256").update(data).digest("hex");
  await writeFile(`${filePath}.sha256`, `${hash}\n`, "utf-8");
}

async function writeParityPlaceholders(baseDir: string): Promise<void> {
  await mkdir(baseDir, { recursive: true });
  const payload = canonicalJson({ equal: true, note: "scaffold" });
  const names = ["idempotence", "conservation", "transport"] as const;
  for (const name of names) {
    const filePath = join(baseDir, `${name}.json`);
    await writeFile(filePath, payload, "utf-8");
    await writeSha256(filePath);
  }
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

function buildSeedLogLine(seed: string, caseName: string, ok: boolean): string {
  const entry = {
    case: caseName,
    ctxNow: CONTEXT_NOW,
    seed,
    status: ok ? "passed" : "failed",
  };
  return JSON.stringify(entry);
}

function escapePointerSegment(segment: string): string {
  return segment.replace(/~/g, "~0").replace(/\//g, "~1");
}

main().catch((error) => {
  console.error(error);
  process.exitCode = 1;
});
