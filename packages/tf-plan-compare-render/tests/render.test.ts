// @tf-test kind=product area=plan speed=fast deps=node
import { describe, expect, it } from 'vitest';
import demoSpec from '../../../tests/specs/demo.json' with { type: 'json' };
import { enumeratePlan } from '@tf-lang/tf-plan-enum';
import { createScaffoldPlan } from '@tf-lang/tf-plan-scaffold-core';
import { buildCompareReport } from '@tf-lang/tf-plan-compare-core';
import { validateCompare } from '@tf-lang/tf-plan-core';
import { renderHtml, renderMarkdown } from '../src/index.js';

describe('tf-plan-compare-render golden output', () => {
  it('produces deterministic artefacts validated against the schema', () => {
    const plan = enumeratePlan(demoSpec, { seed: 42, beamWidth: 2, maxBranches: 2 });
    const scaffold = createScaffoldPlan(plan.nodes, plan.meta, { template: 'dual-stack', top: 2 });
    const report = buildCompareReport(plan.nodes, scaffold, { seed: 42 });
    validateCompare(report);

    const htmlFirst = renderHtml(report);
    const htmlSecond = renderHtml(report);
    expect(htmlFirst).toEqual(htmlSecond);
    const specHash = scaffold.meta.specHash;
    const htmlSnapshot = htmlFirst.replaceAll(specHash, '<SPEC_HASH>');
    expect(htmlSnapshot).toMatchInlineSnapshot(`
"<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\" />\n<meta http-equiv=\"Content-Security-Policy\" content=\"default-src 'none'; style-src 'unsafe-inline'; img-src 'self' data:; connect-src 'none'; script-src 'none'; object-src 'none'; base-uri 'none'; form-action 'none'; frame-ancestors 'none';\" />\n<title>tf-plan comparison</title>\n<style>\n  body { font-family: system-ui, sans-serif; padding: 1rem; background-color: #f8fafc; color: #111827; }\n  h1 { margin-top: 0; }\n  table { border-collapse: collapse; width: 100%; margin-bottom: 1.5rem; background-color: #ffffff; }\n  th, td { border: 1px solid #d1d5db; padding: 0.5rem 0.75rem; text-align: left; vertical-align: top; }\n  th { background-color: #e5e7eb; font-weight: 600; }\n  section { margin-bottom: 1.5rem; }\n  ul { padding-left: 1.25rem; }\n  .oracle-name { font-weight: 600; }\n  .oracle-status { font-variant: small-caps; }\n</style>\n</head><body>\n  <h1>tf-plan comparison (version 0.1.0)</h1>\n  <p><strong>Seed:</strong> 42<br /><strong>Spec Hash:</strong> <SPEC_HASH></p>\n  <table>\n    <thead><tr><th>Rank</th><th>Branch</th><th>Total</th><th>Risk</th><th>Summary</th></tr></thead>\n    <tbody><tr><td>1</td><td>t4/dual-stack/b7e8b3ebecdb</td><td>6.54</td><td>3.60</td><td>t4/dual-stack/b7e8b3ebecdb ranks #1 with total 6.54 (risk 3.60)</td></tr><tr><td>2</td><td>t4/dual-stack/d9c6d9cad0d1</td><td>6.53</td><td>3.52</td><td>t4/dual-stack/d9c6d9cad0d1 ranks #2 with total 6.53 (risk 3.52)</td></tr></tbody>\n  </table>\n  <section><h2>Notes</h2><ul><li>branches=2</li></ul></section>\n  <section><h3>t4/dual-stack/b7e8b3ebecdb</h3><ul><li>No oracle results available</li></ul></section><section><h3>t4/dual-stack/d9c6d9cad0d1</h3><ul><li>No oracle results available</li></ul></section>\n</body></html>"
    `);

    const markdown = renderMarkdown(report);
    const markdownSnapshot = markdown.replaceAll(specHash, '<SPEC_HASH>');
    expect(markdownSnapshot).toBe(
      `# tf-plan comparison (version 0\\.1\\.0)\n\n*Seed:* 42 *Spec Hash:* <SPEC_HASH>\n\n| Rank | Branch | Total | Risk | Notes |\n| --- | --- | --- | --- | --- |\n| 1 | t4/dual\\-stack/b7e8b3ebecdb | 6\\.54 | 3\\.60 | t4/dual\\-stack/b7e8b3ebecdb ranks \\#1 with total 6\\.54 \\(risk 3\\.60\\) |\n| 2 | t4/dual\\-stack/d9c6d9cad0d1 | 6\\.53 | 3\\.52 | t4/dual\\-stack/d9c6d9cad0d1 ranks \\#2 with total 6\\.53 \\(risk 3\\.52\\) |\n\n### t4/dual\\-stack/b7e8b3ebecdb\n- No oracle results available\n\n### t4/dual\\-stack/d9c6d9cad0d1\n- No oracle results available\n`
    );
  });
});
