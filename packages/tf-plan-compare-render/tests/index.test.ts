import { describe, expect, it } from 'vitest';
import { CompareReport } from '@tf-lang/tf-plan-compare-core';
import { renderHtml, renderMarkdown } from '../src/index.js';

const report: CompareReport = {
  version: '0.1.0',
  meta: { seed: 42, specHash: 'demo1234', planVersion: '0.1.0', generatedAt: '1970-01-01T00:00:00.000Z', notes: [] },
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
      "# tf-plan comparison (version 0.1.0)

      *Seed:* 42 *Spec Hash:* demo1234

      | Rank | Branch | Total | Risk | Notes |
      | --- | --- | --- | --- | --- |
      | 1 | t4/demo | 9.00 | 2.00 | top branch |

      ### t4/demo
      - No oracle results available
      "
    `);
  });

  it('renders html deterministically', () => {
    const html = renderHtml(report);
    expect(html).toMatchInlineSnapshot(`
      "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\" /><title>tf-plan comparison</title><meta http-equiv=\"Content-Security-Policy\" content=\"default-src 'none'; style-src 'self' 'unsafe-inline'; img-src 'self' data:; font-src 'self'; form-action 'none'; base-uri 'self'; frame-ancestors 'none';\"><style>body{font-family:system-ui,sans-serif;padding:1rem;background:#fdfdfd;color:#1a1a1a;}table{border-collapse:collapse;width:100%;margin-bottom:1.5rem;}th,td{border:1px solid #d0d0d0;padding:0.5rem;text-align:left;}th{background-color:#efefef;}h1{margin-top:0;}section{margin-bottom:1.5rem;}section h3{margin-bottom:0.5rem;}</style></head><body><h1>tf-plan comparison (version 0.1.0)</h1><p><strong>Seed:</strong> 42 · <strong>Spec Hash:</strong> demo1234</p><table aria-describedby=\"summary\"><thead><tr><th scope=\"col\">Rank</th><th scope=\"col\">Branch</th><th scope=\"col\">Total</th><th scope=\"col\">Risk</th><th scope=\"col\">Summary</th></tr></thead><tbody><tr><td>1</td><td>t4/demo</td><td>9.00</td><td>2.00</td><td>top branch</td></tr></tbody></table><div id=\"summary\"><section><h3>t4/demo</h3><ul><li>No oracle results available</li></ul></section></div></body></html>"
    `);
  });
});
