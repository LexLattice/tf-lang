import assert from 'node:assert/strict';
import { runTransform } from '../index.mjs';
import { mintTokenDeterministic, checkTokenDeterministic } from '../../ops/auth.mjs';

const payload = { amount: 250, currency: 'USD' };
const key = 'agent-secret';

const signature = runTransform({ op: 'auth.sign' }, { key, payload });
assert.match(signature.signature, /^[0-9a-f]+$/);

const verify = runTransform({ op: 'auth.verify' }, { key, payload, signature: signature.signature });
assert.equal(verify.valid, true);

const claims = { sub: 'acct:123', scope: ['payments:write'] };
const alg = 'blake3';
const token = runTransform({ op: 'auth.mint_token', alg }, { secret: 'shared-secret', claims });
const canonical = mintTokenDeterministic({ secret: 'shared-secret', claims, alg });
assert.equal(token.token, canonical.token);
assert.deepEqual(token.claims, canonical.claims);

const check = runTransform({ op: 'auth.check_token', alg }, { secret: 'shared-secret', claims, token: token.token });
assert.equal(check.valid, true);
assert.equal(checkTokenDeterministic(token.token, { secret: 'shared-secret', claims, alg }), true);

console.log('auth transforms OK');
