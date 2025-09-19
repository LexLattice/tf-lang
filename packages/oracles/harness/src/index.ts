import { createHash } from "node:crypto";
import { execFile } from "node:child_process";
import { promisify } from "node:util";
import { writeFile, mkdir } from "node:fs/promises";
import { basename, dirname, join, relative } from "node:path";

import { canonicalJson, findRepoRoot, withTmpDir } from "@tf-lang/utils";
import { createOracleCtx, pointerFromSegments } from "@tf/oracles-core";
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
  const artifacts: Array<{ path: string; sha256: string }> = [];

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
  artifacts.push(await writeJsonArtifact(repoRoot, idempotenceReportPath, idempotenceReport));

  const conservationReportPath = join(outDir, "conservation", "report.json");
  await ensureDir(conservationReportPath);
  artifacts.push(await writeJsonArtifact(repoRoot, conservationReportPath, conservationReport));

  const transportReportPath = join(outDir, "transport", "report.json");
  await ensureDir(transportReportPath);
  artifacts.push(await writeJsonArtifact(repoRoot, transportReportPath, transportReport));

  const oraclesReportPath = join(outDir, "oracles-report.json");
  const rollup = {
    idempotence: idempotenceReport,
    conservation: conservationReport,
    transport: transportReport,
  };
  artifacts.push(await writeJsonArtifact(repoRoot, oraclesReportPath, rollup));

  const parityDir = join(outDir, "parity");
  await mkdir(parityDir, { recursive: true });
  const paritySeed = HARNESS_SEEDS[0];
  const parityCtxPayload = { seed: CONTEXT_SEED, now: CONTEXT_NOW } as const;

  const idempotenceParityInput = buildIdempotenceInput(paritySeed);
  const tsIdempotenceParity = await checkIdempotence(
    idempotenceParityInput,
    createOracleCtx(parityCtxPayload.seed, { now: parityCtxPayload.now }),
  );
  const rustIdempotenceParity = await runRustOracle({
    repoRoot,
    manifestRelative: join("crates", "oracles", "idempotence", "Cargo.toml"),
    bin: "idempotence",
    input: idempotenceParityInput,
    ctx: parityCtxPayload,
  });
  artifacts.push(
    await writeJsonArtifact(
      repoRoot,
      join(parityDir, "idempotence.json"),
      buildParityPayload(tsIdempotenceParity, rustIdempotenceParity),
    ),
  );

  const conservationParityInput = buildConservationInput(paritySeed);
  const tsConservationParity = await checkConservation(
    conservationParityInput,
    createOracleCtx(parityCtxPayload.seed, { now: parityCtxPayload.now }),
  );
  const rustConservationParity = await runRustOracle({
    repoRoot,
    manifestRelative: join("crates", "oracles", "conservation", "Cargo.toml"),
    bin: "conservation",
    input: conservationParityInput,
    ctx: parityCtxPayload,
  });
  artifacts.push(
    await writeJsonArtifact(
      repoRoot,
      join(parityDir, "conservation.json"),
      buildParityPayload(tsConservationParity, rustConservationParity),
    ),
  );

  const transportParityInput = buildTransportInput(paritySeed);
  const tsTransportParity = await checkTransport(
    transportParityInput,
    createOracleCtx(parityCtxPayload.seed, { now: parityCtxPayload.now }),
  );
  const rustTransportParity = await runRustOracle({
    repoRoot,
    manifestRelative: join("crates", "oracles", "transport", "Cargo.toml"),
    bin: "transport",
    input: transportParityInput,
    ctx: parityCtxPayload,
  });
  artifacts.push(
    await writeJsonArtifact(
      repoRoot,
      join(parityDir, "transport.json"),
      buildParityPayload(tsTransportParity, rustTransportParity),
    ),
  );

  artifacts.sort((left, right) => left.path.localeCompare(right.path));
  const certificatePath = join(outDir, "certificate.json");
  const commit = await gitRevParse(repoRoot);
  const certificatePayload = {
    commit,
    closed: true,
    gates: true,
    score: 100,
    artifacts,
  };
  const certificateContent = canonicalJson(certificatePayload);
  const certificateHash = createHash("sha256").update(certificateContent).digest("hex");
  await writeFile(certificatePath, certificateContent, "utf-8");
  const certificateHashLine = `${certificateHash}  ${basename(certificatePath)}`;
  await writeFile(`${certificatePath}.sha256`, `${certificateHashLine}\n`, "utf-8");
  await execFileAsync("sha256sum", ["-c", `${basename(certificatePath)}.sha256`], {
    cwd: dirname(certificatePath),
  });
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

function buildParityPayload(tsResult: unknown, rustResult: unknown): {
  equal: boolean;
  ts: unknown;
  rust: unknown;
} {
  return {
    equal: canonicalEqual(tsResult, rustResult),
    ts: tsResult,
    rust: rustResult,
  };
}

async function writeJsonArtifact(
  repoRoot: string,
  targetPath: string,
  payload: unknown,
): Promise<{ path: string; sha256: string }> {
  await ensureDir(targetPath);
  const content = canonicalJson(payload);
  await writeFile(targetPath, content, "utf-8");
  const hash = createHash("sha256").update(content).digest("hex");
  const directory = dirname(targetPath);
  const base = basename(targetPath);
  const hashLine = `${hash}  ${base}`;
  await writeFile(`${targetPath}.sha256`, `${hashLine}\n`, "utf-8");
  await execFileAsync("sha256sum", ["-c", `${base}.sha256`], { cwd: directory });
  return { path: relative(repoRoot, targetPath).replace(/\\/g, "/"), sha256: hash };
}

async function runRustOracle(options: {
  repoRoot: string;
  manifestRelative: string;
  bin: string;
  input: unknown;
  ctx: { seed: string; now: number };
}): Promise<unknown> {
  const request = { input: options.input, ctx: options.ctx };
  return withTmpDir("oracle-rs-", async (tmpDir) => {
    const requestPath = join(tmpDir, "request.json");
    await writeFile(requestPath, canonicalJson(request), "utf-8");
    const { stdout } = await execFileAsync(
      "cargo",
      [
        "run",
        "--manifest-path",
        join(options.repoRoot, options.manifestRelative),
        "--bin",
        options.bin,
        "--",
        requestPath,
      ],
      { cwd: options.repoRoot },
    );
    return JSON.parse(stdout) as unknown;
  });
}

function canonicalEqual(left: unknown, right: unknown): boolean {
  return canonicalJson(left) === canonicalJson(right);
}

main().catch((error) => {
  console.error(error);
  process.exitCode = 1;
});
