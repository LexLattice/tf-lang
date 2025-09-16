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
import { runValidate } from "../src/cli.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const fixture = path.join(here, "../fixtures/sample-spec.json");

function readJson(file: string): unknown {
  return JSON.parse(readFileSync(file, "utf-8"));
}

async function captureStream<T>(
  stream: NodeJS.WriteStream,
  fn: () => Promise<T>
): Promise<{ result: T; output: string }> {
  const chunks: string[] = [];
  const originalWrite = stream.write;
  (stream.write as typeof stream.write) = ((chunk: string | Uint8Array, encoding?: BufferEncoding | ((error?: Error | null) => void), callback?: (error?: Error | null) => void) => {
    const text = typeof chunk === "string"
      ? chunk
      : chunk.toString(typeof encoding === "string" ? encoding : undefined);
    chunks.push(text);
    if (typeof encoding === "function") {
      encoding();
    } else if (typeof callback === "function") {
      callback();
    }
    return true;
  }) as typeof stream.write;
  try {
    const result = await fn();
    return { result, output: chunks.join("") };
  } finally {
    stream.write = originalWrite;
  }
}

function captureStdout<T>(fn: () => Promise<T>): Promise<{ result: T; output: string }> {
  return captureStream(process.stdout, fn);
}

function captureStderr<T>(fn: () => Promise<T>): Promise<{ result: T; output: string }> {
  return captureStream(process.stderr, fn);
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

  it("supports inline CLI flag values", async () => {
    const cwd = process.cwd();
    process.chdir(path.join(here, ".."));
    try {
      const { result: exitCode, output } = await captureStdout(() =>
        runValidate(["--input=fixtures/sample-spec.json"])
      );
      expect(exitCode).toBe(0);
      expect(output).toContain('"status": "ok"');
    } finally {
      process.chdir(cwd);
    }
  });

  it("fails on unknown CLI flags", async () => {
    const { result: exitCode, output } = await captureStderr(() =>
      runValidate([`--input=${fixture}`, "--bogus"])
    );
    expect(exitCode).toBe(2);
    expect(output).toContain("unknown flag: --bogus");
  });

  it("fails when flag values are missing", async () => {
    const { result: exitCode, output } = await captureStderr(() =>
      runValidate(["--input"])
    );
    expect(exitCode).toBe(2);
    expect(output).toContain("missing value for --input");
  });
});
