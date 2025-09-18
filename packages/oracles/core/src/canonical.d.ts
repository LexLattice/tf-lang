export type Canonicalizer = <T>(value: T) => T;
export declare const defaultCanonicalize: Canonicalizer;
export declare function canonicalStringify(value: unknown): string;
