// @tf-test kind=product area=transform speed=fast deps=node

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { runTransform } from '../index.mjs';

test('jsonschema.validate rejects string schema IDs', () => {
  assert.throws(
    () => runTransform({ op: 'jsonschema.validate', schema: 'FnolV1' }, { value: {} }),
    /not supported/
  );
});
