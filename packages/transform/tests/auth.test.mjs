import assert from 'node:assert/strict';
import { runTransform } from '../index.mjs';

const payload = { amount: 250, currency: 'USD' };
const key = 'agent-secret';

const signature = runTransform({ op: 'auth.sign' }, { key, payload });
assert.match(signature.signature, /^[0-9a-f]+$/);

const verify = runTransform({ op: 'auth.verify' }, { key, payload, signature: signature.signature });
assert.equal(verify.valid, true);

const claims = { sub: 'acct:123', scope: ['payments:write'] };
const token = runTransform({ op: 'auth.mint_token' }, { secret: 'shared-secret', claims });
assert.ok(token.token.startsWith('tok_'));

const check = runTransform({ op: 'auth.check_token' }, { secret: 'shared-secret', claims, token: token.token });
assert.equal(check.valid, true);

console.log('auth transforms OK');
