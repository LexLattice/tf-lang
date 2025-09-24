export interface WrapAuthorizeRange {
  start?: number;
  end?: number;
}

export interface WrapAuthorizeResult {
  newText: string;
  start: number;
  end: number;
  before: string;
  after: string;
}

export function wrapWithAuthorize(
  src: string,
  range?: WrapAuthorizeRange
): WrapAuthorizeResult;
