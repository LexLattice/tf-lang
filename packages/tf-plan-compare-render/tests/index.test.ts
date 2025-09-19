import { describe, expect, it } from 'vitest';
import { CompareReport } from '@tf-lang/tf-plan-compare-core';
import { renderHtml, renderMarkdown } from '../src/index.js';

const report: CompareReport = {
  version: '0.1.0',
  meta: {
    seed: 42,
    specHash: 'demo-spec-hash',
    planVersion: '0.1.0',
    generatedAt: '1970-01-01T00:00:00.000Z',
    notes: ['branches=1'],
  },
  branches: [
    {
      nodeId: 'node',
      branchName: 't4/demo',
      planChoice: 'choice',
      rank: 1,
      score: { total: 9, risk: 2, complexity: 4, perf: 6, devTime: 5, depsReady: 7 },
      summary: 'top branch',
      oracles: [],
    },
  ],
};

describe('renderers', () => {
  it('renders markdown deterministically', () => {
    const md = renderMarkdown(report);
    expect(md).toMatchInlineSnapshot(`
      "# tf-plan comparison (version 0.1.0)\n\n*Seed:* 42  \n*Spec hash:* demo-spec-hash  \n*Plan version:* 0.1.0  \n*Generated at:* 1970-01-01T00:00:00.000Z\n\n| Rank | Branch | Total | Risk | Summary |\n| --- | --- | --- | --- | --- |\n| 1 | t4/demo | 9.00 | 2.00 | top branch |\n\n### t4/demo\n- No oracle results available\n\n- branches=1"
    `);
  });

  it('renders html deterministically', () => {
    const html = renderHtml(report);
    expect(html).toContain("Content-Security-Policy");
    expect(html).toContain('Spec hash:');
  });
});
