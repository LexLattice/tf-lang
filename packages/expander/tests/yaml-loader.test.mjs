// @tf-test kind=product area=expander speed=fast deps=node

import assert from 'node:assert/strict';
import { loadYamlDocument } from '../yaml-loader.mjs';

const source = `
pipeline: demo.pipeline
inputs:
  - receive: interaction.receive(endpoint: "api/demo", qos: "at_least_once")
steps:
  - validate: transform.validate(schema: "Demo", input: "@receive.body") # inline comment should be ignored
  - infer: transform.model_infer(
      model: "demo.v1",
      input: { sample: "@receive.body" }
    )
  - branch:
      when: "@infer.score > 0.5"
      then:
        - audit: policy.record_decision(kind: "demo.check", payload: "@infer")
metadata: { owner: "demo", version: 1 }
`;

const doc = loadYamlDocument(source);

assert.equal(doc.pipeline, 'demo.pipeline');
assert.equal(doc.inputs[0].receive, 'interaction.receive(endpoint: "api/demo", qos: "at_least_once")');
assert.equal(doc.steps[0].validate, 'transform.validate(schema: "Demo", input: "@receive.body")');
assert.equal(
  doc.steps[1].infer,
  'transform.model_infer(\n      model: "demo.v1",\n      input: { sample: "@receive.body" }\n    )',
);
assert.equal(doc.metadata.owner, 'demo');
assert.equal(doc.metadata.version, 1);

const branchStep = doc.steps[2].branch;
assert.equal(branchStep.when, "@infer.score > 0.5");
assert.equal(branchStep.then[0].audit, 'policy.record_decision(kind: "demo.check", payload: "@infer")');

console.log('yaml loader handles macros with comments and multi-line arguments');
