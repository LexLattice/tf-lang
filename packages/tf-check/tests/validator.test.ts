import { Buffer } from "node:buffer";
import { mkdtempSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";

import { describe, expect, it } from "vitest";

import {
  canonicalJson,
  validateSpec,
  validateSpecFile,
  writeArtifacts,
} from "../src/index.js";
import { runCli } from "../src/cli.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const fixture = path.join(here, "../fixtures/sample-spec.json");

function readJson(file: string): unknown {
  return JSON.parse(readFileSync(file, "utf-8"));
}

function makeWriter(chunks: string[]): typeof process.stdout.write {
  return ((
    chunk: string | Uint8Array,
    encoding?: BufferEncoding | ((error?: Error | null) => void),
    callback?: (error?: Error | null) => void
  ) => {
    let finalCallback: ((error?: Error | null) => void) | undefined;
    let normalized: string;
    if (typeof encoding === "function") {
      finalCallback = encoding;
    } else {
      finalCallback = callback;
    }
    if (typeof chunk === "string") {
      normalized = chunk;
    } else {
      const enc = typeof encoding === "string" ? encoding : "utf8";
      normalized = Buffer.from(chunk).toString(enc);
    }
    chunks.push(normalized);
    if (finalCallback) finalCallback(null);
    return true;
  }) as typeof process.stdout.write;
}

async function runCliWithCapture(
  args: string[],
  options: { cwd?: string } = {}
): Promise<{ code: number; stdout: string; stderr: string }> {
  const stdoutChunks: string[] = [];
  const stderrChunks: string[] = [];
  const originalStdout = process.stdout.write;
  const originalStderr = process.stderr.write;
  const originalCwd = process.cwd();
  if (options.cwd) {
    process.chdir(options.cwd);
  }
  process.stdout.write = makeWriter(stdoutChunks);
  process.stderr.write = makeWriter(stderrChunks);
  try {
    const code = await runCli(args);
    return { code, stdout: stdoutChunks.join(""), stderr: stderrChunks.join("") };
  } finally {
    process.stdout.write = originalStdout;
    process.stderr.write = originalStderr;
    if (options.cwd) {
      process.chdir(originalCwd);
    }
  }
}

describe("tf-check validation", () => {
  it("validates a known-good spec", async () => {
    const result = await validateSpecFile(fixture);
    expect(result.status).toBe("ok");
    if (result.status !== "ok") return;
    expect(result.summary.stepCount).toBe(3);
    expect(result.summary.operations).toEqual({
      copy: 1,
      create_network: 1,
      create_vm: 1,
    });
  });

  it("reports unknown operations", () => {
    const spec = {
      version: "0.1",
      name: "bad",
      steps: [
        { op: "mystery", params: {} },
      ],
    };
    const result = validateSpec(spec);
    expect(result.status).toBe("error");
    if (result.status !== "error") return;
    expect(result.error.code).toBe("E_SPEC_OP_UNKNOWN");
    expect(result.error.path).toBe("/steps/0/op");
    expect(result.error.message).toBe("E_SPEC_OP_UNKNOWN /steps/0/op");
  });

  it("maps schema errors from tf-lang-l0", () => {
    const spec = {
      name: "missing version",
      steps: [],
    };
    const result = validateSpec(spec);
    expect(result.status).toBe("error");
    if (result.status !== "error") return;
    expect(result.error.code).toBe("E_SPEC_VERSION");
    expect(result.error.path).toBe("/version");
    expect(result.error.message).toBe("E_SPEC_VERSION /version");
  });

  it("writes canonical artifacts", async () => {
    const dir = mkdtempSync(path.join(tmpdir(), "tf-check-"));
    try {
      await writeArtifacts({ outDir: dir, inputPath: fixture });
      const help = readFileSync(path.join(dir, "help.txt"), "utf-8");
      expect(help.startsWith("tf-check")).toBe(true);
      const result = readJson(path.join(dir, "result.json"));
      expect(result).toMatchObject({ status: "ok" });
      const normalized = canonicalJson(result);
      expect(normalized.endsWith("\n")).toBe(true);
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });

  it("supports equals syntax for CLI flags", async () => {
    const pkgRoot = path.join(here, "..");
    const { code, stdout, stderr } = await runCliWithCapture(
      ["validate", "--input=fixtures/sample-spec.json"],
      { cwd: pkgRoot }
    );
    expect(stderr).toBe("");
    expect(code).toBe(0);
    const parsed = JSON.parse(stdout) as { status: string };
    expect(parsed.status).toBe("ok");
  });

  it("fails on unknown CLI flags", async () => {
    const { code, stderr } = await runCliWithCapture([
      "validate",
      "--input",
      fixture,
      "--wat",
      "nope",
    ]);
    expect(code).toBe(2);
    expect(stderr).toContain("unknown flag: --wat");
  });

  it("reports missing flag values", async () => {
    const { code, stderr } = await runCliWithCapture(["validate", "--input"]);
    expect(code).toBe(2);
    expect(stderr).toContain("missing value for --input");
  });
});
