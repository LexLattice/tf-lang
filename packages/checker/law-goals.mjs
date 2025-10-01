export const LAW_GOALS = [
  {
    id: 'branch-exclusive',
    key: 'branch_exclusive',
    name: 'Branch exclusivity',
    description: 'Branch guards with opposite outcomes never overlap in the same pipeline branch.',
    evidenceKind: 'smt2',
  },
  {
    id: 'monotonic-log',
    key: 'monotonic_log',
    name: 'Monotonic log publishing',
    description: 'Log channels append new entries with strictly increasing positions and do not rewrite prior entries.',
  },
  {
    id: 'confidential-envelope',
    key: 'confidential_envelope',
    name: 'Confidential envelopes',
    description: 'Encrypted envelopes are emitted without exposing parallel plaintext payloads.',
  },
  {
    id: 'idempotency',
    key: 'idempotency',
    name: 'RPC idempotency',
    description: 'RPC requests with stable correlation identifiers execute idempotently.',
    evidenceKind: 'smt2',
  },
  {
    id: 'rpc-pairing',
    key: 'rpc_pairing',
    name: 'RPC pairing',
    description: 'Request/response pairs share reply channels and correlation identifiers.',
  },
  {
    id: 'state-merge',
    key: 'crdt_merge',
    name: 'State merge strategy',
    description: 'State merge transforms expose which algebraic laws apply to the configured strategy.',
  },
];

export const LAW_GOALS_BY_ID = new Map(LAW_GOALS.map((goal) => [goal.id, goal]));
export const LAW_GOALS_BY_KEY = new Map(LAW_GOALS.map((goal) => [goal.key, goal]));
