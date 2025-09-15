import { readFileSync, readdirSync } from "fs";
import { fileURLToPath } from "url";
import path from "path";
import { parseSpec, serializeSpec } from "../src/spec/adapter.js";
import { canonicalJsonBytes } from "../src/canon/json.js";
import { describe, it, expect } from "vitest";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const examplesDir = path.resolve(__dirname, "../../../examples/specs");

const files = readdirSync(examplesDir).filter(f => f.endsWith(".json"));

describe("tf-spec examples", () => {
  for (const file of files) {
    it(file, () => {
      const data = readFileSync(path.join(examplesDir, file));
      const spec = parseSpec(data);
      const out = serializeSpec(spec);
      const expected = canonicalJsonBytes(JSON.parse(data.toString()));
      expect(Buffer.from(out)).toStrictEqual(Buffer.from(expected));
    });
  }
});

describe("tf-spec validation", () => {
  it("rejects unknown op", () => {
    const bad = {
      version: "0.1",
      name: "bad",
      steps: [{ op: "nope", params: {} }]
    };
    expect(() => parseSpec(bad)).toThrow("E_SPEC_OP_UNKNOWN: nope");
  });

  it("rejects missing params", () => {
    const bad = {
      version: "0.1",
      name: "bad",
      steps: [{ op: "copy", params: { src: "a" } }]
    };
    expect(() => parseSpec(bad)).toThrow(
      "E_SPEC_PARAM_MISSING: steps[0].params.dest"
    );
  });

  it("rejects extra params", () => {
    const bad = {
      version: "0.1",
      name: "bad",
      steps: [{ op: "copy", params: { src: "a", dest: "b", extra: 1 } }]
    };
    expect(() => parseSpec(bad)).toThrow(
      "E_SPEC_PARAM_EXTRA: steps[0].params.extra"
    );
  });

  it("rejects cpus < 1", () => {
    const bad = {
      version: "0.1",
      name: "bad",
      steps: [{ op: "create_vm", params: { image: "img", cpus: 0 } }]
    };
    expect(() => parseSpec(bad)).toThrow(
      "E_SPEC_PARAM_INVALID: steps[0].params.cpus"
    );
  });
});
