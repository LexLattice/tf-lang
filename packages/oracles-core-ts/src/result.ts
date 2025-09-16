export interface OracleResult {
  ok: boolean;
  code?: string;
  message?: string;
  path?: string; // RFC6901 JSON Pointer
  evidence?: unknown;
}

export const codeMessages: Record<string, string> = {
  E_NOT_EQUAL: "values are not equal",
  E_NOT_SUBSET: "object is not a subset of expected",
  E_OUT_OF_RANGE: "value is out of range",
  E_REGEX_MISMATCH: "value does not match regex",
  E_EMPTY: "value is empty",
  E_FIELD_UNKNOWN: "unknown field present"
};

