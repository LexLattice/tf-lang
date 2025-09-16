import { mkdtempSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";

import { describe, expect, it, vi } from "vitest";

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

  it("accepts equals syntax for required flags", async () => {
    const stdout = vi.spyOn(process.stdout, "write").mockImplementation(() => true);
    const stderr = vi.spyOn(process.stderr, "write").mockImplementation(() => true);
    try {
      const exitCode = await runValidate([`--input=${fixture}`]);
      expect(exitCode).toBe(0);
      expect(stderr).not.toHaveBeenCalled();
    } finally {
      stdout.mockRestore();
      stderr.mockRestore();
    }
  });

  it("rejects unknown flags", async () => {
    const stdout = vi.spyOn(process.stdout, "write").mockImplementation(() => true);
    const stderr = vi.spyOn(process.stderr, "write").mockImplementation(() => true);
    try {
      const exitCode = await runValidate(["--input", fixture, "--oops"]);
      expect(exitCode).toBe(2);
      const messages = stderr.mock.calls.map((call) => String(call[0]));
      expect(messages.join(" ")).toContain("unknown flag: --oops");
    } finally {
      stdout.mockRestore();
      stderr.mockRestore();
    }
  });

  it("errors when a flag value is missing", async () => {
    const stdout = vi.spyOn(process.stdout, "write").mockImplementation(() => true);
    const stderr = vi.spyOn(process.stderr, "write").mockImplementation(() => true);
    try {
      const exitCode = await runValidate(["--input", fixture, "--out"]);
      expect(exitCode).toBe(2);
      const messages = stderr.mock.calls.map((call) => String(call[0]));
      expect(messages.join(" ")).toContain("missing value for --out");
    } finally {
      stdout.mockRestore();
      stderr.mockRestore();
    }
  });
});
