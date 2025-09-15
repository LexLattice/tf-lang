import { canonicalize } from 'json-canonicalize';

export interface Op {
  op: string;
  args?: Op[];
  value?: any;
}

export interface Spec {
  version: '0.1';
  id: string;
  root: Op;
}

export const parse = (json: string): Spec => {
  return JSON.parse(json);
};

export const serialize = (spec: Spec): string => {
  return canonicalize(spec);
};
