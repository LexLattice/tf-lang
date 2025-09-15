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
