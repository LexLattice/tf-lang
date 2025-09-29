// @tf-test kind=unit area=tf-lsp speed=fast deps=none
import assert from 'node:assert/strict';
import test from 'node:test';

import { wrapWithAuthorize } from './wrap-authorize.mjs';

const CASES = [
  {
    name: 'handles leading blank lines with trailing newline',
    before: 'task "example" {\n',
    selection: '\n    alpha();\n      beta();\n',
    after: '}\n',
    expectedReplacement:
      '    authorize{ scope: "" } {\n\n      alpha();\n        beta();\n    }\n',
  },
  {
    name: 'preserves mixed tab and space indentation without final newline',
    before: 'module "mix" {\n',
    selection: '\t  first();\n\t\tsecond();',
    after: '\n}\n',
    expectedReplacement:
      '\t  authorize{ scope: "" } {\n\t    first();\n\t    second();\n\t  }',
  },
  {
    name: 'trims trailing blank lines but keeps final newline intent',
    before: 'config {\n',
    selection: '      gamma();\n\n\n',
    after: '}\n',
    expectedReplacement:
      '      authorize{ scope: "" } {\n        gamma();\n      }\n',
  },
  {
    name: 'drops trailing blank lines without adding a newline',
    before: 'locals {\n',
    selection: '    delta();\n\n   ',
    after: '\n}\n',
    expectedReplacement:
      '    authorize{ scope: "" } {\n      delta();\n    }',
  },
];

for (const { name, before, selection, after, expectedReplacement } of CASES) {
  test(name, () => {
    const source = `${before}${selection}${after}`;
    const range = { start: before.length, end: before.length + selection.length };
    const result = wrapWithAuthorize(source, range);

    assert.equal(result.start, range.start);
    assert.equal(result.end, range.end);
    assert.equal(result.newText, expectedReplacement);

    const applied = `${before}${result.newText}${after}`;
    const expectedDocument = `${before}${expectedReplacement}${after}`;
    assert.equal(applied, expectedDocument);
  });
}
