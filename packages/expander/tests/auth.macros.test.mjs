import assert from 'node:assert/strict';
import { expandPipelineFromYaml } from '../expand.mjs';

const source = `
pipeline: unit.auth
steps:
  - signer: auth.sign(key: "@keypair.private", payload: { claim: "@input" })
  - verifier: auth.verify(key: "@keypair.public", payload: "@input", signature: "@signer.signature", alg: "sha256")
  - minted: auth.mint_token(secret: "@secrets.auth", claims: { sub: "@input.id" }, alg: "blake3")
  - checked: auth.check_token(secret: "@secrets.auth", claims: { sub: "@input.id" }, token: "@minted.token")
`;

const dag = expandPipelineFromYaml(source);

const byId = Object.fromEntries(dag.nodes.map((node) => [node.id, node]));

const signNode = byId.T_signer;
assert.equal(signNode?.kind, 'Transform');
assert.equal(signNode?.spec?.op, 'auth.sign');
assert.equal(signNode?.spec?.alg, undefined);
assert.deepEqual(signNode?.in, {
  key: '@keypair.private',
  payload: { claim: '@input' },
});

const verifyNode = byId.T_verifier;
assert.equal(verifyNode?.spec?.op, 'auth.verify');
assert.equal(verifyNode?.spec?.alg, 'sha256');
assert.deepEqual(verifyNode?.in, {
  key: '@keypair.public',
  payload: '@input',
  signature: '@signer.signature',
});

const mintNode = byId.T_minted;
assert.equal(mintNode?.spec?.op, 'auth.mint_token');
assert.equal(mintNode?.spec?.alg, 'blake3');
assert.deepEqual(mintNode?.in, {
  secret: '@secrets.auth',
  claims: { sub: '@input.id' },
});

const checkNode = byId.T_checked;
assert.equal(checkNode?.spec?.op, 'auth.check_token');
assert.equal(checkNode?.spec?.alg, undefined);
assert.deepEqual(checkNode?.in, {
  secret: '@secrets.auth',
  claims: { sub: '@input.id' },
  token: '@minted.token',
});

console.log('auth macros expand to kernel transforms');
