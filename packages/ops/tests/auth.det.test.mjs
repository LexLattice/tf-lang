// @tf-test kind=product area=ops speed=fast deps=node

import assert from 'node:assert/strict';
import { mintTokenDeterministic, checkTokenDeterministic } from '../auth.mjs';
import { runTransform } from '../../transform/index.mjs';
import executeL0 from '../../runtime/run.mjs';

const secret = 'shared-secret';
const claims = { sub: 'acct:123', scope: ['payments:write'] };
const alg = 'blake3';

const minted = mintTokenDeterministic({ secret, claims, alg });
assert.ok(minted.token.startsWith('tok_'));
assert.equal(checkTokenDeterministic(minted.token, { secret, claims, alg }), true);

const transformToken = runTransform({ op: 'auth.mint_token', alg }, { secret, claims });
assert.equal(transformToken.token, minted.token);
assert.deepEqual(transformToken.claims, minted.claims);

const pipeline = {
  nodes: [
    {
      id: 'T_token',
      kind: 'Transform',
      spec: { op: 'auth.mint_token', alg },
      in: { secret, claims },
      out: { var: 'token' },
    },
  ],
};

const { context } = await executeL0(pipeline);
assert.equal(context.token.token, minted.token);
assert.deepEqual(context.token.claims, minted.claims);

console.log('auth deterministic helpers OK');
