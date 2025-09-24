export interface WrapAuthorizeEdit {
  newText: string;
  start: number;
  end: number;
  before: string;
  after: string;
}

export interface WrapAuthorizeRange {
  start?: number;
  end?: number;
}

export function wrapWithAuthorize(src: string, range?: WrapAuthorizeRange): WrapAuthorizeEdit;
