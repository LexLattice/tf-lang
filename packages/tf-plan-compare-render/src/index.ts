import { CompareReport } from '@tf-lang/tf-plan-compare-core';
import { validateCompare } from '@tf-lang/tf-plan-core';

type CompareBranchData = CompareReport['branches'][number];
type CompareOracleData = CompareBranchData['oracles'][number];

function escapeHtml(input: unknown): string {
  return String(input)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}

function escapeMarkdown(text: string): string {
  const escaped = text.replace(/[\\`*_{}\[\]()#+\-.!|]/g, (char) => `\\${char}`);
  return escaped.replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

function formatScore(value: number, label: string): string {
  if (!Number.isFinite(value)) {
    throw new Error(`${label} must be a finite number, received ${value}`);
  }
  return value.toFixed(2);
}

function sanitizeBranchSummary(summary: string): string {
  return escapeHtml(summary);
}

function renderOracleList(branch: CompareBranchData): string {
  if (branch.oracles.length === 0) {
    return '<li>No oracle results available</li>';
  }

  return branch.oracles
    .map((oracle: CompareOracleData) => {
      const parts = [
        `<span class="oracle-name">${escapeHtml(oracle.name)}</span>`,
        `<span class="oracle-status">${escapeHtml(oracle.status)}</span>`,
      ];
      if (oracle.details) {
        parts.push(`<span class="oracle-details">${escapeHtml(oracle.details)}</span>`);
      }
      if (oracle.artifact) {
        parts.push(`<span class="oracle-artifact">artifact: ${escapeHtml(oracle.artifact)}</span>`);
      }
      return `<li>${parts.join(' — ')}</li>`;
    })
    .join('');
}

export function renderMarkdown(report: CompareReport): string {
  const valid = validateCompare<CompareReport>(report);
  const header = `# tf-plan comparison (version ${escapeMarkdown(valid.version)})\n\n`;
  const metaLines = [`*Seed:* ${escapeMarkdown(String(valid.meta.seed))}`, `*Spec Hash:* ${escapeMarkdown(valid.meta.specHash)}`];
  const meta = `${metaLines.join(' ')}\n\n`;
  const tableHeader = '| Rank | Branch | Total | Risk | Notes |\n| --- | --- | --- | --- | --- |\n';
  const tableRows = valid.branches
    .map((branch: CompareBranchData) => {
      const rank = escapeMarkdown(String(branch.rank));
      const name = escapeMarkdown(branch.branchName);
      const total = escapeMarkdown(formatScore(branch.score.total, 'total score'));
      const risk = escapeMarkdown(formatScore(branch.score.risk, 'risk score'));
      const summary = escapeMarkdown(branch.summary);
      return `| ${rank} | ${name} | ${total} | ${risk} | ${summary} |`;
    })
    .join('\n');
  const oracleSection = valid.branches
    .map((branch: CompareBranchData) => {
      const name = escapeMarkdown(branch.branchName);
      if (branch.oracles.length === 0) {
        return `### ${name}\n- No oracle results available\n`;
      }
      const oracleLines = branch.oracles
        .map((oracle: CompareOracleData) => {
          const segments = [`- ${escapeMarkdown(oracle.name)}: ${escapeMarkdown(oracle.status)}`];
          if (oracle.details) {
            segments.push(escapeMarkdown(oracle.details));
          }
          if (oracle.artifact) {
            segments.push(`artifact ${escapeMarkdown(oracle.artifact)}`);
          }
          return segments.join(' ');
        })
        .join('\n');
      return `### ${name}\n${oracleLines}\n`;
    })
    .join('\n');
  return `${header}${meta}${tableHeader}${tableRows}\n\n${oracleSection}`;
}

export function renderHtml(report: CompareReport): string {
  const valid = validateCompare<CompareReport>(report);
  const rows = valid.branches
    .map((branch: CompareBranchData) => {
      const columns = [
        escapeHtml(branch.rank),
        escapeHtml(branch.branchName),
        escapeHtml(formatScore(branch.score.total, 'total score')),
        escapeHtml(formatScore(branch.score.risk, 'risk score')),
        sanitizeBranchSummary(branch.summary),
      ];
      const cells = columns.map((column) => `<td>${column}</td>`).join('');
      return `<tr>${cells}</tr>`;
    })
    .join('');

  const oracleBlocks = valid.branches
    .map((branch: CompareBranchData) => {
      const items = renderOracleList(branch);
      return `<section><h3>${escapeHtml(branch.branchName)}</h3><ul>${items}</ul></section>`;
    })
    .join('');

  const notes = valid.meta.notes?.map((note: string) => `<li>${escapeHtml(note)}</li>`).join('') ?? '';
  const notesSection = notes ? `<section><h2>Notes</h2><ul>${notes}</ul></section>` : '';

  return `<!doctype html><html lang="en"><head><meta charset="utf-8" />
<meta http-equiv="Content-Security-Policy" content="default-src 'none'; style-src 'unsafe-inline'; img-src 'self' data:; connect-src 'none'; script-src 'none'; object-src 'none'; base-uri 'none'; form-action 'none'; frame-ancestors 'none';" />
<title>tf-plan comparison</title>
<style>
  body { font-family: system-ui, sans-serif; padding: 1rem; background-color: #f8fafc; color: #111827; }
  h1 { margin-top: 0; }
  table { border-collapse: collapse; width: 100%; margin-bottom: 1.5rem; background-color: #ffffff; }
  th, td { border: 1px solid #d1d5db; padding: 0.5rem 0.75rem; text-align: left; vertical-align: top; }
  th { background-color: #e5e7eb; font-weight: 600; }
  section { margin-bottom: 1.5rem; }
  ul { padding-left: 1.25rem; }
  .oracle-name { font-weight: 600; }
  .oracle-status { font-variant: small-caps; }
</style>
</head><body>
  <h1>tf-plan comparison (version ${escapeHtml(valid.version)})</h1>
  <p><strong>Seed:</strong> ${escapeHtml(valid.meta.seed)}<br /><strong>Spec Hash:</strong> ${escapeHtml(valid.meta.specHash)}</p>
  <table>
    <thead><tr><th>Rank</th><th>Branch</th><th>Total</th><th>Risk</th><th>Summary</th></tr></thead>
    <tbody>${rows}</tbody>
  </table>
  ${notesSection}
  ${oracleBlocks}
</body></html>`;
}
