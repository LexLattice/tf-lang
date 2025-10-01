// @tf-test kind=infra area=tools speed=fast deps=node

import test from "node:test";
import assert from "node:assert/strict";
import { mkdtempSync, writeFileSync, readdirSync, readFileSync } from "node:fs";
import { join } from "node:path";
import os from "node:os";
import { spawnSync } from "node:child_process";

function writePipeline(tmpDir, name, pipeline) {
  const filePath = join(tmpDir, name);
  writeFileSync(filePath, JSON.stringify(pipeline, null, 2), "utf8");
  return filePath;
}

test("typecheck reports OK for pipelines without types", () => {
  const tmp = mkdtempSync(join(os.tmpdir(), "tf-typecheck-ok-"));
  const okPipeline = {
    pipeline_id: "cli.typecheck.ok",
    nodes: [
      {
        id: "S_plain",
        kind: "Subscribe",
        channel: "rpc:req:noop",
        qos: "at_least_once",
        out: { var: "msg" },
      },
    ],
  };
  const file = writePipeline(tmp, "ok.l0.json", okPipeline);

  const result = spawnSync("node", ["tools/tf-lang-cli/index.mjs", "typecheck", file], {
    cwd: process.cwd(),
    encoding: "utf8",
  });

  assert.equal(result.status, 0, `expected exit code 0, got ${result.status}`);
  assert.equal(result.stdout.trim(), "OK");
});

test("typecheck surfaces adapter suggestions with nested paths", () => {
  const tmp = mkdtempSync(join(os.tmpdir(), "tf-typecheck-suggest-"));
  const pipeline = {
    pipeline_id: "cli.typecheck.suggest",
    nodes: [
      {
        id: "S_fnol",
        kind: "Subscribe",
        channel: "rpc:req:fnol",
        qos: "at_least_once",
        out: {
          var: "fnol_csv",
          type: { schemaRef: "FnolV1", format: "csv" },
        },
        metadata: {
          port_types: {
            out: {
              fnol_csv: { schemaRef: "FnolV1", format: "csv" },
            },
          },
        },
      },
      {
        id: "T_needs_json",
        kind: "Transform",
        spec: { op: "extract" },
        in: {
          payload: {
            claim: "@fnol_csv",
          },
        },
        metadata: {
          port_types: {
            in: {
              payload: {
                claim: { schemaRef: "FnolV1", format: "json" },
              },
            },
          },
        },
      },
    ],
  };
  const file = writePipeline(tmp, "suggest.l0.json", pipeline);

  const result = spawnSync("node", ["tools/tf-lang-cli/index.mjs", "typecheck", file], {
    cwd: process.cwd(),
    encoding: "utf8",
  });

  assert.equal(result.status, 0, `expected exit code 0, got ${result.status}`);
  const out = result.stdout.trim().split(/\n/);
  assert.equal(out[0], "OK with 1 suggestion(s)");
  assert.equal(out.length, 2);
  assert.equal(
    out[1],
    " - T_needs_json.in.payload.claim: fnol_csv (FnolV1 (csv)) → FnolV1 (json) via Transform(op: adapter.fnol_csv_to_json)"
  );
});

test("typecheck returns failures when adapters are missing", () => {
  const tmp = mkdtempSync(join(os.tmpdir(), "tf-typecheck-fail-"));
  const pipeline = {
    pipeline_id: "cli.typecheck.fail",
    nodes: [
      {
        id: "S_fnol",
        kind: "Subscribe",
        channel: "rpc:req:fnol",
        qos: "at_least_once",
        out: {
          var: "fnol_csv",
          type: { schemaRef: "FnolV1", format: "csv" },
        },
        metadata: {
          port_types: {
            out: {
              fnol_csv: { schemaRef: "FnolV1", format: "csv" },
            },
          },
        },
      },
      {
        id: "T_needs_xml",
        kind: "Transform",
        spec: { op: "extract" },
        in: {
          payload: {
            claim: "@fnol_csv",
          },
        },
        metadata: {
          port_types: {
            in: {
              payload: {
                claim: { schemaRef: "FnolV1", format: "xml" },
              },
            },
          },
        },
      },
    ],
  };
  const file = writePipeline(tmp, "fail.l0.json", pipeline);

  const result = spawnSync("node", ["tools/tf-lang-cli/index.mjs", "typecheck", file], {
    cwd: process.cwd(),
    encoding: "utf8",
  });

  assert.equal(result.status, 1, `expected exit code 1, got ${result.status}`);
  const out = result.stdout.trim().split(/\n/);
  assert.equal(out[0], "FAILED with 1 mismatch(es)");
  assert.equal(out.length, 2);
  assert.equal(
    out[1],
    " - T_needs_xml.in.payload.claim: fnol_csv (FnolV1 (csv)) → FnolV1 (xml)"
  );
});

test("typecheck emits adapter stubs when requested", () => {
  const tmp = mkdtempSync(join(os.tmpdir(), "tf-typecheck-emit-"));
  const emitDir = join(tmp, "stubs");
  const pipeline = {
    pipeline_id: "cli.typecheck.emit",
    nodes: [
      {
        id: "S_fnol",
        kind: "Subscribe",
        channel: "rpc:req:fnol",
        qos: "at_least_once",
        out: {
          var: "fnol_csv",
          type: { schemaRef: "FnolV1", format: "csv" }
        },
        metadata: {
          port_types: {
            out: {
              fnol_csv: { schemaRef: "FnolV1", format: "csv" }
            }
          }
        }
      },
      {
        id: "T_needs_xml",
        kind: "Transform",
        spec: { op: "extract" },
        in: { value: "@fnol_csv" },
        metadata: {
          port_types: {
            in: { value: { schemaRef: "FnolV1", format: "xml" } }
          }
        }
      }
    ]
  };
  const file = writePipeline(tmp, "emit.l0.json", pipeline);

  const result = spawnSync(
    "node",
    ["tools/tf-lang-cli/index.mjs", "typecheck", file, "--emit-adapters", emitDir],
    {
      cwd: process.cwd(),
      encoding: "utf8"
    }
  );

  assert.equal(result.status, 1, `expected exit code 1, got ${result.status}`);
  const out = result.stdout.trim().split(/\n/);
  assert.equal(out[0], "FAILED with 1 mismatch(es)");
  assert.equal(out[1], " - T_needs_xml.in.value: fnol_csv (FnolV1 (csv)) → FnolV1 (xml)");
  assert.equal(out[2], `Emitted 1 adapter stub(s) to ${emitDir}`);
  const files = readdirSync(emitDir);
  assert.equal(files.length, 1);
  const stub = readFileSync(join(emitDir, files[0]), "utf8");
  assert(stub.includes("@generated by tf typecheck --emit-adapters"));
});
