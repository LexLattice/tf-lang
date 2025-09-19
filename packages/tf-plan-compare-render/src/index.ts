import { CompareReport } from '@tf-lang/tf-plan-compare-core';
import { validateCompare } from '@tf-lang/tf-plan-core';

const STYLE = `
  body { font-family: system-ui, sans-serif; margin: 0 auto; max-width: 960px; padding: 1.5rem; background: #f9fafb; color: #111827; }
  h1 { margin-bottom: 1rem; font-size: 1.75rem; }
  p.meta { margin: 0.25rem 0; }
  table { border-collapse: collapse; width: 100%; margin: 1.5rem 0; background: #ffffff; box-shadow: 0 1px 2px rgba(15, 23, 42, 0.1); }
  th, td { border: 1px solid #e5e7eb; padding: 0.5rem 0.75rem; text-align: left; vertical-align: top; }
  th { background: #f3f4f6; font-weight: 600; }
  section { background: #ffffff; padding: 1rem; margin-bottom: 1rem; border: 1px solid #e5e7eb; border-radius: 0.5rem; box-shadow: 0 1px 2px rgba(15, 23, 42, 0.05); }
  section h3 { margin-top: 0; }
  ul { padding-left: 1.25rem; }
  .notes { margin: 0.5rem 0 1rem 0; padding-left: 1.25rem; }
  .notes li { list-style: disc; }
`;

const CSP = "default-src 'none'; style-src 'self' 'unsafe-inline'; img-src 'self' data:; connect-src 'none'; font-src 'none'; frame-src 'none'; form-action 'none'; base-uri 'none';";

const HTML_ESCAPES: Record<string, string> = {
  '&': '&amp;',
  '<': '&lt;',
  '>': '&gt;',
  '"': '&quot;',
  "'": '&#39;',
};

function escapeHtml(value: string): string {
  return value.replace(/[&<>"'\u2028\u2029]/g, (match) => HTML_ESCAPES[match] ?? `&#${match.charCodeAt(0)};`);
}

function escapeMarkdown(value: string): string {
  return value.replace(/[\\|*_`\[\]<>]/g, (match) => `\\${match}`);
}

function formatNumber(value: number): string {
  if (!Number.isFinite(value)) {
    throw new Error(`Non-finite number encountered while rendering: ${value}`);
  }
  return value.toFixed(2);
}

function ensureReport(report: CompareReport): CompareReport {
  return validateCompare(report);
}

function renderOracleListHtml(report: CompareReport): string {
  return report.branches
    .map((branch) => {
      const oracleItems = branch.oracles.length
        ? branch.oracles
            .map((oracle) => {
              const segments = [escapeHtml(oracle.status)];
              if (oracle.details) {
                segments.push(escapeHtml(oracle.details));
              }
              if (oracle.artifact) {
                segments.push(`artifact: ${escapeHtml(oracle.artifact)}`);
              }
              return `<li><strong>${escapeHtml(oracle.name)}</strong>: ${segments.join(' · ')}</li>`;
            })
            .join('')
        : '<li>No oracle results available</li>';
      return `<section><h3>${escapeHtml(branch.branchName)}</h3><ul>${oracleItems}</ul></section>`;
    })
    .join('');
}

function renderNotesHtml(notes: readonly string[] | undefined): string {
  if (!notes || notes.length === 0) {
    return '';
  }
  const items = notes.map((note) => `<li>${escapeHtml(note)}</li>`).join('');
  return `<ul class="notes">${items}</ul>`;
}

export function renderMarkdown(input: CompareReport): string {
  const report = ensureReport(input);
  const header = `# tf-plan comparison (version ${escapeMarkdown(report.version)})`;
  const metaLines = [
    `*Seed:* ${escapeMarkdown(String(report.meta.seed))}`,
    `*Spec hash:* ${escapeMarkdown(report.meta.specHash)}`,
    `*Plan version:* ${escapeMarkdown(report.meta.planVersion)}`,
    `*Generated at:* ${escapeMarkdown(report.meta.generatedAt)}`,
  ];
  const tableHeader = '| Rank | Branch | Total | Risk | Summary |\n| --- | --- | --- | --- | --- |';
  const tableRows = report.branches
    .map(
      (branch) =>
        `| ${branch.rank} | ${escapeMarkdown(branch.branchName)} | ${formatNumber(branch.score.total)} | ${formatNumber(branch.score.risk)} | ${escapeMarkdown(branch.summary)} |`,
    )
    .join('\n');
  const oracleSection = report.branches
    .map((branch) => {
      if (branch.oracles.length === 0) {
        return `### ${escapeMarkdown(branch.branchName)}\n- No oracle results available`;
      }
      const oracleLines = branch.oracles
        .map((oracle) => {
          const details: string[] = [escapeMarkdown(oracle.status)];
          if (oracle.details) {
            details.push(escapeMarkdown(oracle.details));
          }
          if (oracle.artifact) {
            details.push(`artifact: ${escapeMarkdown(oracle.artifact)}`);
          }
          return `- ${escapeMarkdown(oracle.name)}: ${details.join(' · ')}`;
        })
        .join('\n');
      return `### ${escapeMarkdown(branch.branchName)}\n${oracleLines}`;
    })
    .join('\n\n');
  const notesSection = report.meta.notes && report.meta.notes.length > 0 ? `\n\n${report.meta.notes.map((note) => `- ${escapeMarkdown(note)}`).join('\n')}` : '';
  return `${header}\n\n${metaLines.join('  \n')}\n\n${tableHeader}\n${tableRows}\n\n${oracleSection}${notesSection}`;
}

export function renderHtml(input: CompareReport): string {
  const report = ensureReport(input);
  const rows = report.branches
    .map((branch) => {
      const cells = [
        String(branch.rank),
        escapeHtml(branch.branchName),
        formatNumber(branch.score.total),
        formatNumber(branch.score.risk),
        escapeHtml(branch.summary),
      ];
      return `<tr>${cells.map((cell) => `<td>${cell}</td>`).join('')}</tr>`;
    })
    .join('');

  const metaNotes = renderNotesHtml(report.meta.notes);
  const oracleBlocks = renderOracleListHtml(report);

  const parts = [
    '<!doctype html>',
    '<html lang="en">',
    '<head>',
    '<meta charset="utf-8" />',
    `<meta http-equiv="Content-Security-Policy" content="${CSP}" />`,
    '<title>tf-plan comparison</title>',
    `<style>${STYLE}</style>`,
    '</head>',
    '<body>',
    `<h1>tf-plan comparison (version ${escapeHtml(report.version)})</h1>`,
    `<p class="meta"><strong>Seed:</strong> ${escapeHtml(String(report.meta.seed))}</p>`,
    `<p class="meta"><strong>Spec hash:</strong> ${escapeHtml(report.meta.specHash)}</p>`,
    `<p class="meta"><strong>Plan version:</strong> ${escapeHtml(report.meta.planVersion)}</p>`,
    `<p class="meta"><strong>Generated at:</strong> ${escapeHtml(report.meta.generatedAt)}</p>`,
    metaNotes,
    '<table>',
    '<thead><tr><th>Rank</th><th>Branch</th><th>Total</th><th>Risk</th><th>Summary</th></tr></thead>',
    `<tbody>${rows}</tbody>`,
    '</table>',
    oracleBlocks,
    '</body>',
    '</html>',
  ];

  return parts.filter((segment) => segment.length > 0).join('');
}
