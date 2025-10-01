import { ensurePublishNodes } from './_util.mjs';

const GOAL_ID = 'monotonic-log';
const TARGET_CHANNELS = new Set(['policy:record']);

function isRef(value) {
  return typeof value === 'string' && value.startsWith('@') && value.length > 1;
}

function describeRef(value) {
  if (typeof value !== 'string') return null;
  return value;
}

function normalizeIssues(issues = []) {
  return Array.from(new Set(issues));
}

export function checkMonotonicLog(options = {}) {
  const publishEntries = ensurePublishNodes(options);
  const varMeta = options.varMeta instanceof Map ? options.varMeta : new Map();
  const results = [];
  const duplicateTracker = new Map();

  for (const entry of publishEntries) {
    const node = entry.node ?? null;
    if (!node || typeof node !== 'object') {
      continue;
    }
    const channel = typeof node.channel === 'string' ? node.channel : null;
    if (!channel || !TARGET_CHANNELS.has(channel)) {
      continue;
    }

    const payload = node.payload && typeof node.payload === 'object' ? node.payload : {};
    const recordIdValue = payload.record_id ?? payload.recordId ?? (payload.entry && payload.entry.id);
    const recordIdRef = describeRef(recordIdValue);
    const recordIdVar = isRef(recordIdRef) ? recordIdRef.slice(1) : null;
    const recordMeta = recordIdVar ? varMeta.get(recordIdVar) : null;

    let indexValue = payload.index;
    let indexSource = 'payload.index';
    if (indexValue === undefined && payload.entry && typeof payload.entry === 'object') {
      indexValue = payload.entry.index;
      indexSource = 'payload.entry.index';
    }
    if (indexValue === undefined) {
      indexValue = payload.ts;
      indexSource = 'payload.ts';
    }
    const indexRef = describeRef(indexValue);
    const indexVar = isRef(indexRef) ? indexRef.slice(1) : null;
    const indexMeta = indexVar ? varMeta.get(indexVar) : null;

    const issues = [];
    if (!recordIdRef) {
      issues.push('record-id-missing');
    } else if (!recordIdVar) {
      issues.push('record-id-static');
    } else {
      if (recordMeta && recordMeta.stable === false) {
        issues.push('record-id-unstable');
      }
      if (recordMeta && recordMeta.deterministic === false) {
        issues.push('record-id-nondeterministic');
      }
    }

    if (!indexRef) {
      issues.push('index-missing');
    } else if (!indexVar) {
      issues.push('index-static');
    } else {
      if (indexMeta && indexMeta.stable === false) {
        issues.push('index-unstable');
      }
      if (indexMeta && indexMeta.deterministic === false) {
        issues.push('index-nondeterministic');
      }
    }

    const result = {
      goal: GOAL_ID,
      id: node.id ?? null,
      channel,
      recordId: recordIdRef ?? null,
      indexRef: indexRef ?? null,
      indexSource: indexRef ? indexSource : null,
      assumption: indexVar ? 'producer-strict-index' : recordIdVar ? 'record-id-unique' : null,
      status: 'PASS',
      ok: true,
      reason: null,
      issues: normalizeIssues(issues),
    };

    if (!recordIdVar && typeof recordIdRef === 'string') {
      const key = `${channel}::${recordIdRef}`;
      if (!duplicateTracker.has(key)) duplicateTracker.set(key, []);
      duplicateTracker.get(key).push(result);
    }

    if (result.issues.length > 0) {
      result.status = 'WARN';
      [result.reason] = result.issues;
    }

    results.push(result);
  }

  for (const [, entries] of duplicateTracker) {
    if (entries.length > 1) {
      for (const entry of entries) {
        entry.status = 'ERROR';
        entry.ok = false;
        entry.issues = normalizeIssues([...entry.issues, 'duplicate-record-id']);
        entry.reason = 'duplicate-record-id';
      }
    }
  }

  const ok = results.every((entry) => entry.ok);
  return {
    goal: GOAL_ID,
    ok,
    results,
  };
}

export default checkMonotonicLog;
