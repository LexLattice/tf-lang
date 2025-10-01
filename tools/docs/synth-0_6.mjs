#!/usr/bin/env node
import { promises as fs } from 'fs';
import path from 'path';

const REVIEW_ROOT = path.resolve('out/0.6/review');
const SKIP_DIRS = new Set(['_summary', '_issues', '_proposals', '_synthesis']);

const CANONICAL_SECTIONS = [
  { key: 'what-exists', heading: '## What exists now', synonyms: ['what exists now', 'current state', 'today'] },
  { key: 'how-to-run', heading: '## How to run (10-minute quickstart)', synonyms: ['how to run', 'quickstart', 'runbook'] },
  { key: 'errors', heading: '## Common errors & fixes', synonyms: ['common errors', 'troubleshooting', 'errors'] },
  { key: 'acceptance', heading: '## Acceptance gates & signals', synonyms: ['acceptance', 'quality gates', 'gates'] },
  { key: 'dx-gaps', heading: '## DX gaps', synonyms: ['dx gaps', 'gaps', 'pain points', 'issues'] },
  { key: 'top-issues', heading: '## Top issues (synthesized)', synonyms: ['top issues', 'key issues', 'priorities'] },
  { key: 'next-improvements', heading: '## Next 3 improvements', synonyms: ['next 3 improvements', 'next steps', 'improvements'] },
  { key: 'references', heading: '## References', synonyms: ['references', 'links'] }
];

const severityHeuristics = [
  { match: /(block|fails|broken|crash|prevent|cannot|missing)/i, value: 'S2' },
  { match: /(critical|severe)/i, value: 'S1' },
  { match: /(docs|documentation|clarity|confus)/i, value: 'S3' },
];

const areaHeuristics = [
  { match: /(doc|guide|readme|spec)/i, value: 'docs' },
  { match: /(schema|cli|tool|expand|validate|runtime|macro|registry|transform)/i, value: 'dx' },
  { match: /(release|ship|gate)/i, value: 'release' }
];

function normalizeHeading(raw) {
  return raw.toLowerCase().replace(/[^a-z0-9]+/g, ' ').trim();
}

function normalizeIssue(text) {
  return text.toLowerCase().replace(/[^a-z0-9]+/g, ' ').trim();
}

function dedupe(items) {
  const seen = new Set();
  const out = [];
  for (const item of items) {
    const norm = normalizeIssue(item);
    if (!norm || seen.has(norm)) continue;
    seen.add(norm);
    out.push(item.trim());
  }
  return out;
}

function parseMarkdownSections(content) {
  const lines = content.split(/\r?\n/);
  const sections = [];
  let current = { title: '__intro__', lines: [] };
  for (const line of lines) {
    const m = line.match(/^(#{2,})\s+(.*)$/);
    if (m) {
      sections.push(current);
      current = { title: m[2].trim(), level: m[1].length, lines: [] };
    } else {
      current.lines.push(line);
    }
  }
  sections.push(current);
  const map = new Map();
  for (const section of sections) {
    const norm = normalizeHeading(section.title);
    map.set(norm, section);
  }
  return { sections, map };
}

function pickSections(sectionMap, synonyms) {
  const results = [];
  for (const key of sectionMap.map.keys()) {
    for (const syn of synonyms) {
      if (normalizeHeading(key).includes(normalizeHeading(syn))) {
        const section = sectionMap.map.get(key);
        if (section) results.push(section);
      }
    }
  }
  return results;
}

function gatherBulletItems(section) {
  if (!section) return [];
  const items = [];
  let buffer = [];
  for (const line of section.lines) {
    const bulletMatch = line.match(/^(\s*)([-*+]|\d+\.)\s+/);
    if (bulletMatch) {
      const indent = bulletMatch[1].length;
      if (indent > 2 && buffer.length) {
        const continuation = line.slice(bulletMatch[0].length).trim();
        if (continuation) buffer.push(continuation);
        continue;
      }
      if (buffer.length) {
        const raw = buffer.join(' ').replace(/\s+/g, ' ').trim();
        if (raw) items.push(raw);
        buffer = [];
      }
      const text = line.slice(bulletMatch[0].length).trim();
      if (text) buffer.push(text);
    } else if (buffer.length) {
      const continuation = line.trim().replace(/^[-*+]\s+/, '').trim();
      if (continuation) buffer.push(continuation);
    }
  }
  if (buffer.length) {
    const raw = buffer.join(' ').replace(/\s+/g, ' ').trim();
    if (raw) items.push(raw);
  }
  return items;
}

function gatherBulletsFromSections(sections) {
  const all = [];
  for (const section of sections) {
    all.push(...gatherBulletItems(section));
  }
  return all;
}

function extractStepsFromSections(sections) {
  const steps = [];
  for (const section of sections) {
    const lines = section.lines;
    let buffer = [];
    let inCode = false;
    let codeLines = [];
    for (const rawLine of lines) {
      const line = rawLine.replace(/^\s+/, '');
      if (line.startsWith('```')) {
        if (inCode) {
          if (codeLines.length) {
            steps.push({
              description: buffer.length ? buffer.join(' ').trim() : 'Run command',
              commands: codeLines.map((cmd) => cmd.trim()).filter(Boolean)
            });
            buffer = [];
          }
          codeLines = [];
          inCode = false;
        } else {
          inCode = true;
        }
        continue;
      }
      if (inCode) {
        const trimmedCmd = line.trim();
        if (trimmedCmd && !trimmedCmd.startsWith('#')) {
          codeLines.push(trimmedCmd);
        }
        continue;
      }
      const trimmed = line.trim();
      if (!trimmed) continue;
      if (/^[-*+]/.test(trimmed) || /^\d+\./.test(trimmed)) {
        buffer = [trimmed.replace(/^[-*+\d\.]+\s+/, '')];
      } else {
        buffer.push(trimmed);
      }
    }
    if (!inCode && buffer.length) {
      const inlineCmdMatch = buffer.join(' ').match(/`([^`]+)`/);
      if (inlineCmdMatch) {
        const command = inlineCmdMatch[1].trim();
        if (command) {
          steps.push({ description: buffer.join(' ').replace(/`([^`]+)`/, '$1').trim(), commands: [command] });
        }
      }
      buffer = [];
    }
  }
  const deduped = [];
  const seen = new Set();
  for (const step of steps) {
    const key = `${step.description}|${step.commands.join(';')}`;
    if (seen.has(key)) continue;
    seen.add(key);
    deduped.push(step);
  }
  return deduped;
}

function describeCommand(cmd) {
  if (!cmd) return 'Run command';
  if (cmd.startsWith('pnpm')) return 'Install workspace dependencies';
  if (cmd.includes('pipeline-expand')) return 'Expand L2 pipeline to L0';
  if (cmd.includes('monitor-expand')) return 'Expand monitor definition';
  if (cmd.includes('plan-instances')) return 'Plan runtime instances';
  if (cmd.includes('typecheck')) return 'Run typechecker';
  if (cmd.includes('tasks/run-examples.sh')) return 'Run v0.6 example suite';
  if (cmd.includes('tf-lang-cli') && cmd.includes('validate')) return 'Validate artifact';
  if (cmd.includes('effects')) return 'Summarize effects';
  if (cmd.includes('graph')) return 'Render DAG graph';
  if (cmd.includes('tf') && cmd.includes('plan-instances')) return 'Plan runtime instances';
  return 'Run command';
}

function parseErrorRow(text) {
  const row = { symptom: '', cause: '', fix: '' };
  const errorMatch = text.match(/\*\*(Error|Symptom)\*\*:\s*([^*]+)/i);
  if (errorMatch) row.symptom = errorMatch[2].trim();
  const causeMatch = text.match(/\*\*(Cause|Reason)\*\*:\s*([^*]+)/i);
  if (causeMatch) row.cause = causeMatch[2].trim();
  const fixMatch = text.match(/\*\*(Fix|Resolution)\*\*:\s*([^*]+)/i);
  if (fixMatch) row.fix = fixMatch[2].trim();
  if (!row.fix) {
    const workaround = text.match(/Workaround:\s*([^.;]+)/i);
    if (workaround) row.fix = workaround[1].trim();
  }
  if (!row.cause) {
    const cause = text.match(/because\s+([^.;]+)/i);
    if (cause) row.cause = `Because ${cause[1].trim()}`;
  }
  if (!row.symptom) {
    const colonIdx = text.indexOf(':');
    if (colonIdx !== -1) {
      row.symptom = text.slice(0, colonIdx).replace(/^[-*\s]+/, '').trim();
      const rest = text.slice(colonIdx + 1).trim();
      if (!row.cause && rest) row.cause = rest;
    } else {
      row.symptom = text.trim();
    }
  }
  if (!row.fix) row.fix = row.cause || 'Document mitigation';
  if (!row.cause) row.cause = 'Investigate root cause';
  return row;
}

function renderTable(rows) {
  if (!rows.length) {
    return ['| Symptom | Probable cause | Fix |', '| --- | --- | --- |', '| – | – | – |'];
  }
  const lines = ['| Symptom | Probable cause | Fix |', '| --- | --- | --- |'];
  for (const row of rows) {
    lines.push(`| ${row.symptom} | ${row.cause} | ${row.fix} |`);
  }
  return lines;
}

function heuristicSeverity(text) {
  for (const rule of severityHeuristics) {
    if (rule.match.test(text)) return rule.value;
  }
  return 'S3';
}

function heuristicArea(text) {
  for (const rule of areaHeuristics) {
    if (rule.match.test(text)) return rule.value;
  }
  return 'dx';
}

function relevanceFromText(text, decision) {
  const sentences = [];
  const area = heuristicArea(text);
  if (decision === 'confirm') {
    sentences.push('Still impacts v0.6 workflows with no documented remediation.');
  } else if (decision === 'defer') {
    sentences.push('Not immediately blocking but worth parking for later follow-up.');
  } else {
    sentences.push('Tracked in earlier drafts but no longer prioritized.');
  }
  if (area === 'docs') {
    sentences.push('Onboarding depends on aligned documentation, so the gap remains visible.');
  } else if (area === 'release') {
    sentences.push('Release gating requires this to flip green before cut.');
  } else {
    sentences.push('Developer workflows continue to encounter the described friction.');
  }
  return sentences.join(' ');
}

async function collectReferences(text, trackDir) {
  const root = path.resolve('.');
  const refs = new Map();
  const pattern = /([A-Za-z0-9_.-]+\/[A-Za-z0-9_.\/-]+)/g;
  let match;
  while ((match = pattern.exec(text))) {
    const candidate = match[1];
    if (candidate.startsWith('http') || candidate.includes('://')) continue;
    if (candidate.startsWith('.')) continue;
    if (candidate.split('/').length < 2) continue;
    const target = path.resolve(root, candidate);
    try {
      await fs.access(target);
    } catch (err) {
      continue;
    }
    if (!refs.has(candidate)) refs.set(candidate, target);
  }
  const lines = [];
  for (const [display, target] of refs.entries()) {
    const rel = path.relative(trackDir, target).replace(/\\/g, '/');
    const href = rel.startsWith('.') ? rel : `./${rel}`;
    lines.push(`- [${display}](${href})`);
  }
  return lines.length ? lines : ['- (none)'];
}

function ensureDir(p) {
  return fs.mkdir(p, { recursive: true });
}

async function walk(dir, pairs) {
  const entries = await fs.readdir(dir, { withFileTypes: true });
  const grouped = new Map();
  for (const entry of entries) {
    if (entry.isDirectory()) {
      if (SKIP_DIRS.has(entry.name)) continue;
      await walk(path.join(dir, entry.name), pairs);
    } else if (entry.isFile()) {
      if (!entry.name.endsWith('.md')) continue;
      const parts = entry.name.split('.');
      if (parts.length < 3) continue;
      const suffix = parts.pop();
      const variant = parts.pop();
      if (suffix !== 'md') continue;
      if (variant !== 'jules' && variant !== 'codex') continue;
      const base = parts.join('.');
      const bucketKey = path.join(dir, base);
      if (!grouped.has(bucketKey)) {
        grouped.set(bucketKey, {});
      }
      grouped.get(bucketKey)[variant] = path.join(dir, entry.name);
    }
  }
  for (const [base, files] of grouped.entries()) {
    if (files.jules && files.codex) {
      pairs.push({ base, jules: files.jules, codex: files.codex });
    }
  }
}

function pickTitle(julesContent, codexContent, trackName) {
  const codexTitle = codexContent.split('\n')[0].trim();
  if (codexTitle.startsWith('#')) return codexTitle;
  const julesTitle = julesContent.split('\n')[0].trim();
  if (julesTitle.startsWith('#')) return julesTitle;
  return `# Track ${trackName}`;
}

function mergeSections(julesSections, codexSections) {
  const merged = new Map();
  for (const section of CANONICAL_SECTIONS) {
    const candidates = [];
    const allJules = julesSections.sections.filter((s) => section.synonyms.some((syn) => normalizeHeading(s.title || '').includes(normalizeHeading(syn))));
    const allCodex = codexSections.sections.filter((s) => section.synonyms.some((syn) => normalizeHeading(s.title || '').includes(normalizeHeading(syn))));
    const combined = [...allJules, ...allCodex];
    if (!combined.length) {
      merged.set(section.key, []);
    } else {
      merged.set(section.key, combined);
    }
  }
  return merged;
}

function makeListLines(items, bullet = '-') {
  return items.map((item) => `${bullet} ${item}`);
}

function buildTopIssues(overlapIssues, uniqueIssues) {
  const prioritized = [...overlapIssues, ...uniqueIssues].slice(0, 3);
  if (!prioritized.length) return ['- Document current blockers in upcoming pass.'];
  return prioritized.map((issue) => `- ${issue.title}`);
}

function buildAcceptanceRows(steps) {
  const rows = [];
  for (const step of steps) {
    for (const cmd of step.commands) {
      rows.push({ gate: cleanDescription(step.description || describeCommand(cmd)), command: cmd, signal: 'Command succeeds without errors.' });
    }
  }
  return rows;
}

function renderAcceptanceTable(rows) {
  if (!rows.length) {
    return ['| Gate | Command | Success signal |', '| --- | --- | --- |', '| – | – | – |'];
  }
  const lines = ['| Gate | Command | Success signal |', '| --- | --- | --- |'];
  for (const row of rows) {
    lines.push(`| ${row.gate} | \`${row.command}\` | ${row.signal} |`);
  }
  return lines;
}

function extractIssuesFromSections(sections, source) {
  const issues = [];
  for (const section of sections) {
    const items = gatherBulletItems(section);
    for (const item of items) {
      const text = item.replace(/^[0-9]+\.?\s*/, '').trim();
      if (!text) continue;
      issues.push({ text, source, section: section.title || '' });
    }
  }
  return issues;
}

function structureIssues(julesIssues, codexIssues) {
  const map = new Map();
  for (const issue of [...julesIssues, ...codexIssues]) {
    const key = normalizeIssue(issue.text);
    if (!map.has(key)) {
      map.set(key, { key, text: issue.text, sources: new Set(), sections: new Set() });
    }
    const entry = map.get(key);
    entry.sources.add(issue.source);
    if (issue.section) entry.sections.add(issue.section);
  }
  const overlapping = [];
  const uniqueJules = [];
  const uniqueCodex = [];
  for (const entry of map.values()) {
    const record = {
      title: entry.text,
      evidence: [],
      severity: heuristicSeverity(entry.text),
      area: heuristicArea(entry.text),
      decision: 'confirm',
    };
    if (entry.sources.has('jules')) record.evidence.push('docs.jules.md §' + Array.from(entry.sections)[0]);
    if (entry.sources.has('codex')) record.evidence.push('docs.codex.md §' + Array.from(entry.sections)[0]);
    record.relevance = relevanceFromText(entry.text, record.decision);
    if (entry.sources.size === 2) {
      overlapping.push(record);
    } else if (entry.sources.has('jules')) {
      uniqueJules.push(record);
    } else {
      uniqueCodex.push(record);
    }
  }
  return { overlapping, uniqueJules, uniqueCodex };
}

function renderIssueList(issues) {
  if (!issues.length) return ['- (none)'];
  const lines = [];
  for (const issue of issues) {
    const title = issue.title.replace(/\*\*/g, '');
    lines.push(`- **${title}**`);
    lines.push(`  - Evidence: ${issue.evidence.join(', ')}`);
    lines.push(`  - Severity: ${issue.severity}`);
    lines.push(`  - Area: ${issue.area}`);
    lines.push(`  - Relevance (${issue.decision}): ${issue.relevance}`);
  }
  return lines;
}

function mapIssueDecisions(issues, sectionName) {
  return issues.map((issue, idx) => `- ${issue.title} → documented in ${sectionName} item ${idx + 1}.`);
}

function cleanDescription(desc) {
  if (!desc) return 'Run command';
  return desc.replace(/\s+/g, ' ').replace(/[:.]*$/, '').trim();
}

function tidyImprovement(text) {
  if (!text) return text;
  const normalized = text.replace(/\s+/g, ' ').trim();
  const titleMatch = normalized.match(/\*\*([^*]+?)(?:\*\*|\*)/);
  let title = '';
  if (titleMatch) {
    title = titleMatch[1].replace(/\*+$/g, '').replace(/\.+$/, '').trim();
  } else {
    title = normalized.split('.')[0].replace(/\*+/g, '').trim();
  }
  const plain = normalized.replace(/\*\*/g, '');
  const actionMatch = plain.match(/Action:\s*(.+?)(?=Impact:|Effort:|$)/i);
  const impactMatch = plain.match(/Impact:\s*(.+?)(?=Effort:|$)/i);
  const effortMatch = plain.match(/Effort:\s*(.+)$/i);
  const parts = [];
  const trimEnd = (value) => value.replace(/[.;]+$/g, '').trim();
  if (actionMatch) parts.push(`Action: ${trimEnd(actionMatch[1])}`);
  if (impactMatch) parts.push(`Impact: ${trimEnd(impactMatch[1])}`);
  if (effortMatch) parts.push(`Effort: ${trimEnd(effortMatch[1])}`);
  let summary = parts.join('; ');
  summary = summary.replace(/\.?;\s*/g, '; ').replace(/;\s*$/g, '');
  if (summary) return `**${title}** — ${summary}`;
  return `**${title}**`;
}

function buildProposal(issue, trackKey, commands) {
  const title = issue.title.replace(/\*\*/g, '').replace(/\.$/, '');
  const lawIntent = issue.area === 'release' ? 'Ensure release gate flips green once command returns success.' : 'Guarantee repeatable outcomes for the described workflow.';
  const pipelineName = `${trackKey.toLowerCase()}-${issue.key || 'fix'}`.slice(0, 40).replace(/[^a-z0-9-]/g, '');
  const acceptanceCommands = (commands && commands.length ? commands : [
    'node tools/tf-lang-cli/index.mjs validate l0 examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json',
    'node tools/tf-lang-cli/index.mjs plan-instances examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json'
  ]).slice(0, 3);
  return [
    `### ${title}`,
    `**Context:** Addresses ${title.toLowerCase()} noted in ${issue.evidence.join(' & ')}.`,
    '**Proposal:**',
    '```yaml',
    `pipeline: "${pipelineName || 'dx-patch'}"`,
    'steps:',
    '  - validate: transform.validate(schema: "schemas/l0-dag.schema.json", input: "@input")',
    '  - request:  interaction.request(endpoint: "@http.mock", method: POST, body: { trace: "@trace" })',
    '  - merge:    state.merge(base_ref: "@input", patch: "@proposal", strategy: "jsonpatch")',
    '```',
    '**Acceptance:**',
    '```bash',
    ...acceptanceCommands,
    '```',
    `**Impact:** ${issue.area === 'docs' ? 'Clarifies contributor workflow and removes ambiguity.' : 'Reduces friction for the core developer workflow.'}`,
    `**Law intent:** ${lawIntent}`,
    '',
  ];
}

async function main() {
  const pairs = [];
  await walk(REVIEW_ROOT, pairs);
  pairs.sort((a, b) => a.base.localeCompare(b.base));
  if (!pairs.length) {
    console.error('No jules/codex pairs found.');
    process.exit(1);
  }
  const synthesisIndex = [];
  const proposalIndex = [];
  for (const pair of pairs) {
    const trackDir = path.dirname(pair.base);
    const trackKey = path.basename(trackDir);
    const julesContent = await fs.readFile(pair.jules, 'utf8');
    const codexContent = await fs.readFile(pair.codex, 'utf8');
    const title = pickTitle(julesContent, codexContent, trackKey);
    const julesSections = parseMarkdownSections(julesContent);
    const codexSections = parseMarkdownSections(codexContent);
    const merged = mergeSections(julesSections, codexSections);

    const whatExists = dedupe(gatherBulletsFromSections(merged.get('what-exists') || []));
    const howToSections = merged.get('how-to-run') || [];
    const steps = extractStepsFromSections(howToSections);
    const commands = dedupe(steps.flatMap((step) => step.commands));
    const errors = dedupe(gatherBulletsFromSections(merged.get('errors') || []));
    const dxGaps = dedupe(gatherBulletsFromSections(merged.get('dx-gaps') || []));
    const improvementsRaw = dedupe(gatherBulletsFromSections(merged.get('next-improvements') || [])).slice(0, 3);
    const improvements = improvementsRaw.map(tidyImprovement);

    const errorRowsAll = errors.map(parseErrorRow);
    const seenSymptoms = new Set();
    const errorRows = [];
    for (const row of errorRowsAll) {
      const key = row.symptom.toLowerCase();
      if (seenSymptoms.has(key)) continue;
      seenSymptoms.add(key);
      errorRows.push(row);
    }
    const acceptanceRows = buildAcceptanceRows(steps);
    const acceptanceTable = renderAcceptanceTable(acceptanceRows);

    const issueSectionsJules = julesSections.sections.filter((s) => normalizeHeading(s.title || '').includes('gap') || normalizeHeading(s.title || '').includes('issue'));
    const issueSectionsCodex = codexSections.sections.filter((s) => normalizeHeading(s.title || '').includes('gap') || normalizeHeading(s.title || '').includes('issue'));
    const structuredIssues = structureIssues(
      extractIssuesFromSections(issueSectionsJules, 'jules'),
      extractIssuesFromSections(issueSectionsCodex, 'codex')
    );
    const topIssues = buildTopIssues(structuredIssues.overlapping, [...structuredIssues.uniqueJules, ...structuredIssues.uniqueCodex]);

    const references = await collectReferences(`${julesContent}\n${codexContent}`, trackDir);

    const howToLines = [];
    if (!steps.length) {
      howToLines.push('1. Review CLI help for track-specific workflows.');
    } else {
      steps.forEach((step, idx) => {
        const description = cleanDescription(step.description || describeCommand(step.commands[0] || ''));
        const suffix = /[.!?]$/.test(description) ? '' : '.';
        howToLines.push(`${idx + 1}. ${description}${suffix}`);
        step.commands.forEach((cmd) => {
          howToLines.push('```bash');
          howToLines.push(cmd);
          howToLines.push('```');
        });
      });
    }

    const finalLines = [];
    finalLines.push(title.startsWith('#') ? title : `# ${title}`);
    finalLines.push('');
    finalLines.push('## What exists now');
    finalLines.push(...(whatExists.length ? makeListLines(whatExists) : ['- Document current assets in next pass.']));
    finalLines.push('');
    finalLines.push('## How to run (10-minute quickstart)');
    finalLines.push(...howToLines);
    finalLines.push('');
    finalLines.push('## Common errors & fixes');
    finalLines.push(...renderTable(errorRows));
    finalLines.push('');
    finalLines.push('## Acceptance gates & signals');
    finalLines.push(...acceptanceTable);
    finalLines.push('');
    finalLines.push('## DX gaps');
    finalLines.push(...(dxGaps.length ? makeListLines(dxGaps) : ['- No DX gaps captured yet.']));
    finalLines.push('');
    finalLines.push('## Top issues (synthesized)');
    finalLines.push(...topIssues);
    finalLines.push('');
    finalLines.push('## Next 3 improvements');
    finalLines.push(...(improvements.length ? makeListLines(improvements) : ['- Populate once priorities are ranked.']));
    finalLines.push('');
    finalLines.push('## References');
    finalLines.push(...references);
    finalLines.push('');

    const finalPath = `${pair.base}.final.md`;
    await fs.writeFile(finalPath, finalLines.join('\n'));

    const synthLines = [];
    synthLines.push(`# Track ${trackKey} · synthesis`);
    synthLines.push('');
    synthLines.push('## Overlapping issues');
    synthLines.push(...renderIssueList(structuredIssues.overlapping));
    synthLines.push('');
    synthLines.push('## Unique to Jules');
    synthLines.push(...renderIssueList(structuredIssues.uniqueJules));
    synthLines.push('');
    synthLines.push('## Unique to Codex');
    synthLines.push(...renderIssueList(structuredIssues.uniqueCodex));
    synthLines.push('');
    synthLines.push('## Decisions applied to .final');
    const decisionLines = [
      ...mapIssueDecisions(structuredIssues.overlapping, '## Top issues (synthesized)'),
      ...mapIssueDecisions(structuredIssues.uniqueJules, '## DX gaps'),
      ...mapIssueDecisions(structuredIssues.uniqueCodex, '## DX gaps')
    ];
    synthLines.push(...(decisionLines.length ? decisionLines : ['- No decisions recorded.']));
    synthLines.push('');
    synthLines.push('---');
    synthLines.push('');
    synthLines.push('**Sources considered:** docs.jules.md, docs.codex.md');
    synthLines.push('');
    synthLines.push('**Dead links fixed:** (pending verification)');
    synthLines.push('');
    synthLines.push('**Open questions:**');
    synthLines.push('- Need follow-up validation once quickstarts are stable.');

    await ensureDir(path.join(REVIEW_ROOT, '_synthesis'));
    const synthPath = path.join(REVIEW_ROOT, '_synthesis', `${trackKey}.synth.md`);
    await fs.writeFile(synthPath, synthLines.join('\n'));

    synthesisIndex.push({ track: trackKey, finalPath: path.relative(path.join(REVIEW_ROOT, '_synthesis'), finalPath), synthPath: `${trackKey}.synth.md` });

    await ensureDir(path.join(REVIEW_ROOT, '_proposals'));
    const proposalLines = [`# Track ${trackKey} · proposals`, ''];
    const confirmedIssues = [...structuredIssues.overlapping, ...structuredIssues.uniqueJules, ...structuredIssues.uniqueCodex];
    const issuesForProposals = confirmedIssues.slice(0, 3);
    if (!issuesForProposals.length) {
      proposalLines.push('- No actionable proposals captured.');
    } else {
      issuesForProposals.forEach((issue) => {
        proposalLines.push(...buildProposal(issue, trackKey, commands));
      });
    }
    const proposalPath = path.join(REVIEW_ROOT, '_proposals', `${trackKey}-proposals.tf.md`);
    await fs.writeFile(proposalPath, proposalLines.join('\n'));
    proposalIndex.push({ track: trackKey, path: path.relative(path.join(REVIEW_ROOT, '_proposals'), proposalPath) });
  }

  await ensureDir(path.join(REVIEW_ROOT, '_synthesis'));
  const indexLines = ['# v0.6 review synthesis index', '', '| Track | Synthesis log | Final doc |', '| --- | --- | --- |'];
  synthesisIndex.sort((a, b) => a.track.localeCompare(b.track));
  for (const item of synthesisIndex) {
    indexLines.push(`| ${item.track} | [${item.track}.synth.md](${item.synthPath}) | [${path.basename(item.finalPath)}](${item.finalPath}) |`);
  }
  await fs.writeFile(path.join(REVIEW_ROOT, '_synthesis', 'INDEX.md'), indexLines.join('\n'));

  await ensureDir(path.join(REVIEW_ROOT, '_proposals'));
  const proposalIdxLines = ['# v0.6 proposals index', '', '| Track | Proposal file | Area |', '| --- | --- | --- |'];
  proposalIndex.sort((a, b) => a.track.localeCompare(b.track));
  for (const item of proposalIndex) {
    proposalIdxLines.push(`| ${item.track} | [${path.basename(item.path)}](${item.path}) | mixed |`);
  }
  await fs.writeFile(path.join(REVIEW_ROOT, '_proposals', 'INDEX.md'), proposalIdxLines.join('\n'));
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
