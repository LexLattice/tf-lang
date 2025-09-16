export type MsgCtx = { min?: number; max?: number; pattern?: string };

export const MESSAGES: Record<string, (ctx?: MsgCtx) => string> = {
  E_OUT_OF_RANGE: ({ min, max } = {}) =>
    `value is out of range${min != null && max != null ? ` [${min}, ${max}]` : ''}`,
  E_EMPTY: () => 'value is empty',
  E_NOT_EQUAL: () => 'values differ',
  E_NOT_SUBSET: () => 'value is not a subset',
  E_REGEX_MISMATCH: ({ pattern } = {}) => `value does not match ${pattern ?? 'pattern'}`,
};

