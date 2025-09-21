import { readFile, writeFile, mkdir } from "node:fs/promises";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

import { fromJSON, toJSON, unify, canonicalStringify } from "../packages/tf-l0-types/src/types.mjs";

const here = dirname(fileURLToPath(import.meta.url));
const specPath = resolve(here, "../packages/tf-l0-spec/spec/signatures.demo.json");
const outputPath = resolve(here, "../out/0.4/check/types-demo.json");

async function loadSpec(path) {
  const raw = await readFile(path, "utf8");
  const data = JSON.parse(raw);
  const entries = Object.entries(data);
  return entries.reduce((acc, [id, payload]) => {
    acc[id] = {
      input: fromJSON(payload.input),
      output: fromJSON(payload.output)
    };
    return acc;
  }, {});
}

function requireSignature(signatures, id) {
  const signature = signatures[id];
  if (!signature) {
    throw new Error(`missing signature for ${id}`);
  }
  return signature;
}

function evaluateChain(signatures, chain) {
  const label = chain.join("|>");
  if (chain.length === 1) {
    const signature = requireSignature(signatures, chain[0]);
    return { chain: label, ok: true, type: toJSON(signature.output) };
  }
  let last = null;
  for (let i = 0; i < chain.length - 1; i += 1) {
    const current = requireSignature(signatures, chain[i]);
    const next = requireSignature(signatures, chain[i + 1]);
    const verdict = unify(current.output, next.input);
    if (!verdict.ok) {
      return { chain: label, ok: false, reason: verdict.reason };
    }
    last = verdict.type;
  }
  const payload = { chain: label, ok: true };
  if (last) {
    payload.type = toJSON(last);
  }
  return payload;
}

async function main() {
  const signatures = await loadSpec(specPath);
  const chains = [
    ["tf:information/hash@1", "tf:information/hash@1"],
    ["tf:network/publish@1", "tf:observability/emit-metric@1"],
    ["tf:resource/write-object@1", "tf:information/hash@1"]
  ];

  const cases = chains.map((chain) => evaluateChain(signatures, chain));
  const summary = cases.reduce(
    (acc, entry) => {
      if (entry.ok) acc.ok += 1;
      else acc.fail += 1;
      return acc;
    },
    { ok: 0, fail: 0 }
  );

  await mkdir(dirname(outputPath), { recursive: true });
  await writeFile(outputPath, `${canonicalStringify({ cases, summary })}\n`);
}

main().catch((err) => {
  console.error(err);
  process.exitCode = 1;
});
