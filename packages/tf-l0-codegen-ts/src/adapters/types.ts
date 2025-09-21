export interface Network {
  publish(topic: string, key: string, payload: string): Promise<void>;
}

export interface Storage {
  writeObject(uri: string, key: string, value: string, idempotencyKey?: string): Promise<void>;
  readObject?(uri: string, key: string): Promise<string | null>;
  compareAndSwap?(uri: string, key: string, expect: string, update: string): Promise<boolean>;
}

export interface Crypto {
  sign(keyId: string, data: Uint8Array): Promise<Uint8Array>;
  verify?(keyId: string, data: Uint8Array, sig: Uint8Array): Promise<boolean>;
  hash?(data: Uint8Array): Promise<string>;
}

export interface Observability {
  emitMetric(name: string, value?: number): Promise<void>;
}

export interface Adapters extends Partial<Crypto & Storage & Network & Observability> {}
