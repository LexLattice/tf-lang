import { CompareReport } from '@tf-lang/tf-plan-compare-core';

export function renderMarkdown(report: CompareReport): string {
  const header = `# tf-plan comparison (version ${report.version})\n\n`;
  const meta = `*Seed:* ${report.meta.seed}\\n\n`;
  const tableHeader = '| Rank | Branch | Total | Risk | Notes |\n| --- | --- | --- | --- | --- |\n';
  const tableRows = report.branches
    .map((branch) => `| ${branch.rank} | ${branch.branchName} | ${branch.score.total.toFixed(2)} | ${branch.score.risk.toFixed(2)} | ${branch.summary} |`)
    .join('\n');
  const oracleSection = report.branches
    .map((branch) => {
      if (branch.oracles.length === 0) {
        return `### ${branch.branchName}\n- No oracle results available\n`;
      }
      const oracleLines = branch.oracles
        .map((oracle) => `- ${oracle.name}: ${oracle.status}${oracle.artifact ? ` ([artifact](${oracle.artifact}))` : ''}`)
        .join('\n');
      return `### ${branch.branchName}\n${oracleLines}\n`;
    })
    .join('\n');
  return `${header}${meta}${tableHeader}${tableRows}\n\n${oracleSection}`;
}

export function renderHtml(report: CompareReport): string {
  const rows = report.branches
    .map(
      (branch) =>
        `<tr><td>${branch.rank}</td><td>${branch.branchName}</td><td>${branch.score.total.toFixed(2)}</td><td>${branch.score.risk.toFixed(2)}</td><td>${branch.summary}</td></tr>`,
    )
    .join('');
  const oracleBlocks = report.branches
    .map((branch) => {
      const items = branch.oracles
        .map((oracle) => {
          const artifact = oracle.artifact ? `<a href="${oracle.artifact}">artifact</a>` : '';
          return `<li><strong>${oracle.name}</strong>: ${oracle.status}${artifact ? ` (${artifact})` : ''}</li>`;
        })
        .join('');
      const fallback = items.length > 0 ? items : '<li>No oracle results available</li>';
      return `<section><h3>${branch.branchName}</h3><ul>${fallback}</ul></section>`;
    })
    .join('');
  return `<!doctype html><html lang="en"><head><meta charset="utf-8" /><title>tf-plan comparison</title><style>
      body { font-family: system-ui, sans-serif; padding: 1rem; }
      table { border-collapse: collapse; width: 100%; margin-bottom: 1rem; }
      th, td { border: 1px solid #ddd; padding: 0.5rem; text-align: left; }
      th { background-color: #f2f2f2; }
    </style></head><body><h1>tf-plan comparison (version ${report.version})</h1>
    <p><strong>Seed:</strong> ${report.meta.seed}</p>
    <table><thead><tr><th>Rank</th><th>Branch</th><th>Total</th><th>Risk</th><th>Summary</th></tr></thead><tbody>${rows}</tbody></table>
    ${oracleBlocks}
    </body></html>`;
}
