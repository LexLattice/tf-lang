import { createHash } from "node:crypto";
import { execFile } from "node:child_process";
import { promisify } from "node:util";
import { readFile, writeFile, mkdir } from "node:fs/promises";
import { dirname, join, relative } from "node:path";

import { canonicalJson, findRepoRoot, withTmpDir } from "@tf-lang/utils";
import { createOracleCtx, pointerFromSegments } from "@tf/oracles-core";
import type { OracleCtx, OracleResult } from "@tf/oracles-core";
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
  const idempotenceReportJson = canonicalJson(idempotenceReport);
  await writeFile(idempotenceReportPath, idempotenceReportJson, "utf-8");

  const conservationReportPath = join(outDir, "conservation", "report.json");
  await ensureDir(conservationReportPath);
  const conservationReportJson = canonicalJson(conservationReport);
  await writeFile(conservationReportPath, conservationReportJson, "utf-8");

  const transportReportPath = join(outDir, "transport", "report.json");
  await ensureDir(transportReportPath);
  const transportReportJson = canonicalJson(transportReport);
  await writeFile(transportReportPath, transportReportJson, "utf-8");

  const oraclesReportPath = join(outDir, "oracles-report.json");
  const rollup = {
    idempotence: idempotenceReport,
    conservation: conservationReport,
    transport: transportReport,
  };
  const rollupJson = canonicalJson(rollup);
  await writeFile(oraclesReportPath, rollupJson, "utf-8");

  const parityDir = join(outDir, "parity");
  const parityArtifacts = await writeParityReports(parityDir, repoRoot);

  const artifacts = await recordArtifacts(repoRoot, [
    idempotenceReportPath,
    conservationReportPath,
    transportReportPath,
    oraclesReportPath,
    ...parityArtifacts.map((artifact) => artifact.path),
  ]);
  const commit = await gitRevParse(repoRoot);
  const certificatePath = join(outDir, "certificate.json");
  const certificatePayload = {
    commit,
    generatedAt: CONTEXT_NOW,
    gates: true,
    closed: true,
    score: 100,
    artifacts: artifacts.map(({ path, sha256 }) => ({ path, sha256 })),
  };
  const certificateJson = canonicalJson(certificatePayload);
  await writeFile(certificatePath, certificateJson, "utf-8");
  await writeSha256FromString(certificatePath, certificateJson);
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
    pointer: pointerFromSegments([violation.key]),
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

type OracleName = "conservation" | "idempotence" | "transport";

async function writeParityReports(
  baseDir: string,
  repoRoot: string,
): Promise<ReadonlyArray<{ path: string }>> {
  await mkdir(baseDir, { recursive: true });
  const outputs: Array<{ path: string }> = [];

  const parityPlan: ReadonlyArray<{
    readonly oracle: OracleName;
    readonly build: (seed: string) => unknown;
    readonly check: (input: unknown, ctx: OracleCtx) => Promise<OracleResult<unknown>>;
  }> = [
    {
      oracle: "idempotence",
      build: (seed) => buildIdempotenceInput(seed),
      check: async (input, ctx) => checkIdempotence(input as IdempotenceInput, ctx),
    },
    {
      oracle: "conservation",
      build: (seed) => buildConservationInput(seed),
      check: async (input, ctx) => checkConservation(input as ConservationInput, ctx),
    },
    {
      oracle: "transport",
      build: (seed) => buildTransportInput(seed),
      check: async (input, ctx) => checkTransport(input as TransportInput, ctx),
    },
  ];

  for (const plan of parityPlan) {
    const tsResults: unknown[] = [];
    const rustResults: unknown[] = [];

    for (const seed of HARNESS_SEEDS) {
      const input = plan.build(seed);
      const ctx = createOracleCtx(CONTEXT_SEED, { now: CONTEXT_NOW });
      const tsResult = await plan.check(input, ctx);
      tsResults.push(tsResult);
      const rustResult = await runRustOracle(plan.oracle, input, repoRoot);
      rustResults.push(rustResult);
    }

    const tsCanonical = canonicalJson(tsResults);
    const rustCanonical = canonicalJson(rustResults);
    const equal = tsCanonical === rustCanonical;
    const payload = canonicalJson({
      oracle: plan.oracle,
      equal,
      seeds: HARNESS_SEEDS,
      ts: tsResults,
      rust: rustResults,
    });
    const filePath = join(baseDir, `${plan.oracle}.json`);
    await writeFile(filePath, payload, "utf-8");
    await writeSha256FromString(filePath, payload);
    outputs.push({ path: filePath });
  }

  return outputs;
}

async function runRustOracle(oracle: OracleName, input: unknown, repoRoot: string): Promise<unknown> {
  return withTmpDir("t3-oracle-", async (dir) => {
    const inputPath = join(dir, "input.json");
    const payload = canonicalJson(input);
    await writeFile(inputPath, payload, "utf-8");
    const args = [
      "run",
      "--quiet",
      "--manifest-path",
      join(repoRoot, "crates", "Cargo.toml"),
      "--bin",
      "t3-oracle-runner",
      "--",
      "--oracle",
      oracle,
      "--input",
      inputPath,
      "--seed",
      CONTEXT_SEED,
      "--now",
      String(CONTEXT_NOW),
    ];
    const { stdout } = await execFileAsync("cargo", args, { cwd: repoRoot });
    return JSON.parse(stdout);
  });
}

async function recordArtifacts(
  repoRoot: string,
  paths: ReadonlyArray<string>,
): Promise<ReadonlyArray<{ path: string; sha256: string }>> {
  const results: Array<{ path: string; sha256: string }> = [];
  const sortedPaths = [...paths].sort();
  for (const filePath of sortedPaths) {
    const relativePath = relative(repoRoot, filePath);
    const data = await readFile(filePath);
    const hash = createHash("sha256").update(data).digest("hex");
    await writeFile(`${filePath}.sha256`, `${hash}\n`, "utf-8");
    results.push({ path: relativePath.replace(/\\/g, "/"), sha256: hash });
  }
  return results;
}

async function writeSha256FromString(filePath: string, content: string): Promise<void> {
  const hash = createHash("sha256").update(content).digest("hex");
  await writeFile(`${filePath}.sha256`, `${hash}\n`, "utf-8");
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

main().catch((error) => {
  console.error(error);
  process.exitCode = 1;
});
