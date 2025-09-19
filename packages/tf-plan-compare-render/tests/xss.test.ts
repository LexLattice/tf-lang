import { describe, expect, it } from 'vitest';
import type { CompareReport } from '@tf-lang/tf-plan-compare-core';
import { renderHtml, renderMarkdown } from '../src/index.js';

const maliciousReport: CompareReport = {
  version: '0.1.0',
  meta: {
    seed: 42,
    planVersion: '0.1.0',
    specHash: 'deadbeef',
    generatedAt: '1970-01-01T00:00:00.000Z',
    notes: ['<script>alert(1)</script>'],
  },
  branches: [
    {
      nodeId: 'node-1',
      branchName: '<script>alert(1)</script>',
      planChoice: 'choice<script>alert(2)</script>',
      rank: 1,
      score: {
        total: 7.5,
        risk: 3.2,
        complexity: 4.1,
        perf: 6.7,
        devTime: 5.3,
        depsReady: 8.1,
      },
      summary: '<img src=x onerror=alert(3)>',
      oracles: [
        {
          name: 'oracle<script>',
          status: 'unknown',
          details: '<b>detail</b>',
          artifact: 'javascript:alert(4)',
        },
      ],
    },
  ],
};

describe('tf-plan-compare-render sanitisation', () => {
  it('escapes potentially dangerous HTML in the renderer output', () => {
    const html = renderHtml(maliciousReport);
    expect(html).not.toContain('<script>');
    expect(html).toContain('&lt;script&gt;alert(1)&lt;/script&gt;');
    expect(html).toContain('&lt;img src=x onerror=alert(3)&gt;');
    expect(html).toContain('artifact: javascript:alert(4)');
    expect(html).toMatchInlineSnapshot(`
"<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\" />\n<meta http-equiv=\"Content-Security-Policy\" content=\"default-src 'none'; style-src 'unsafe-inline'; img-src 'self' data:; connect-src 'none'; script-src 'none'; object-src 'none'; base-uri 'none'; form-action 'none'; frame-ancestors 'none';\" />\n<title>tf-plan comparison</title>\n<style>\n  body { font-family: system-ui, sans-serif; padding: 1rem; background-color: #f8fafc; color: #111827; }\n  h1 { margin-top: 0; }\n  table { border-collapse: collapse; width: 100%; margin-bottom: 1.5rem; background-color: #ffffff; }\n  th, td { border: 1px solid #d1d5db; padding: 0.5rem 0.75rem; text-align: left; vertical-align: top; }\n  th { background-color: #e5e7eb; font-weight: 600; }\n  section { margin-bottom: 1.5rem; }\n  ul { padding-left: 1.25rem; }\n  .oracle-name { font-weight: 600; }\n  .oracle-status { font-variant: small-caps; }\n</style>\n</head><body>\n  <h1>tf-plan comparison (version 0.1.0)</h1>\n  <p><strong>Seed:</strong> 42<br /><strong>Spec Hash:</strong> deadbeef</p>\n  <table>\n    <thead><tr><th>Rank</th><th>Branch</th><th>Total</th><th>Risk</th><th>Summary</th></tr></thead>\n    <tbody><tr><td>1</td><td>&lt;script&gt;alert(1)&lt;/script&gt;</td><td>7.50</td><td>3.20</td><td>&lt;img src=x onerror=alert(3)&gt;</td></tr></tbody>\n  </table>\n  <section><h2>Notes</h2><ul><li>&lt;script&gt;alert(1)&lt;/script&gt;</li></ul></section>\n  <section><h3>&lt;script&gt;alert(1)&lt;/script&gt;</h3><ul><li><span class=\"oracle-name\">oracle&lt;script&gt;</span> — <span class=\"oracle-status\">unknown</span> — <span class=\"oracle-details\">&lt;b&gt;detail&lt;/b&gt;</span> — <span class=\"oracle-artifact\">artifact: javascript:alert(4)</span></li></ul></section>\n</body></html>"
    `);
  });

  it('renders markdown without leaking raw html', () => {
    const markdown = renderMarkdown(maliciousReport);
    expect(markdown).toContain('*Spec Hash:* deadbeef');
    expect(markdown).not.toContain('<script>');
    expect(markdown).toBe(
      `# tf-plan comparison (version 0\\.1\\.0)\n\n*Seed:* 42 *Spec Hash:* deadbeef\n\n| Rank | Branch | Total | Risk | Notes |\n| --- | --- | --- | --- | --- |\n| 1 | &lt;script&gt;alert\\(1\\)&lt;/script&gt; | 7\\.50 | 3\\.20 | &lt;img src=x onerror=alert\\(3\\)&gt; |\n\n### &lt;script&gt;alert\\(1\\)&lt;/script&gt;\n- oracle&lt;script&gt;: unknown &lt;b&gt;detail&lt;/b&gt; artifact javascript:alert\\(4\\)\n`
    );
  });
});
