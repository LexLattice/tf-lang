import { spawn } from 'node:child_process';
import { EventEmitter } from 'node:events';
import { fileURLToPath } from 'node:url';
import { dirname, resolve } from 'node:path';

function toContent(message) {
  const payload = JSON.stringify(message);
  return `Content-Length: ${Buffer.byteLength(payload, 'utf8')}\r\n\r\n${payload}`;
}

export class LspClient extends EventEmitter {
  constructor() {
    super();
    const moduleDir = dirname(fileURLToPath(import.meta.url));
    const serverPath = resolve(moduleDir, '../../packages/tf-lsp-server/bin/server.mjs');
    this.proc = spawn('node', [serverPath, '--stdio'], {
      stdio: ['pipe', 'pipe', 'pipe'],
    });
    this.buffer = '';
    this.nextId = 1;
    this.pending = new Map();

    this.proc.stdout.setEncoding('utf8');
    this.proc.stdout.on('data', (chunk) => {
      this.buffer += chunk;
      this.#processBuffer();
    });

    this.proc.stderr.setEncoding('utf8');
    this.proc.stderr.on('data', (chunk) => {
      if (chunk.trim().length > 0) {
        this.emit('stderr', chunk);
      }
    });

    this.proc.on('exit', (code) => {
      for (const [, resolver] of this.pending) {
        resolver.reject(new Error(`LSP server exited with code ${code ?? 0}`));
      }
      this.pending.clear();
    });
  }

  async initialize(rootUri = null) {
    const params = {
      processId: process.pid,
      rootUri,
      capabilities: {},
    };
    const result = await this.sendRequest('initialize', params);
    await this.sendNotification('initialized', {});
    return result;
  }

  sendRequest(method, params) {
    const id = this.nextId;
    this.nextId += 1;
    const message = { jsonrpc: '2.0', id, method, params };
    const payload = toContent(message);
    this.proc.stdin.write(payload, 'utf8');
    return new Promise((resolve, reject) => {
      this.pending.set(id, { resolve, reject });
    });
  }

  async sendNotification(method, params) {
    const message = { jsonrpc: '2.0', method, params };
    const payload = toContent(message);
    await new Promise((resolve) => this.proc.stdin.write(payload, 'utf8', resolve));
  }

  async shutdown() {
    try {
      await this.sendRequest('shutdown', null);
      await this.sendNotification('exit', null);
    } catch {
      this.proc.kill();
    }
  }

  #processBuffer() {
    while (true) {
      const headerEnd = this.buffer.indexOf('\r\n\r\n');
      if (headerEnd === -1) {
        return;
      }
      const header = this.buffer.slice(0, headerEnd);
      const lengthMatch = /Content-Length: (\d+)/i.exec(header);
      if (!lengthMatch) {
        this.buffer = this.buffer.slice(headerEnd + 4);
        continue;
      }
      const length = Number.parseInt(lengthMatch[1], 10);
      const totalLength = headerEnd + 4 + length;
      if (this.buffer.length < totalLength) {
        return;
      }
      const body = this.buffer.slice(headerEnd + 4, totalLength);
      this.buffer = this.buffer.slice(totalLength);
      try {
        const message = JSON.parse(body);
        this.#handleMessage(message);
      } catch (error) {
        this.emit('error', error);
      }
    }
  }

  #handleMessage(message) {
    if (typeof message.id === 'number' && this.pending.has(message.id)) {
      const { resolve, reject } = this.pending.get(message.id);
      this.pending.delete(message.id);
      if ('error' in message) {
        reject(new Error(String(message.error?.message ?? 'Unknown error')));
        return;
      }
      resolve(message.result);
      return;
    }
    if (message.method) {
      this.emit('notification', message);
      if (message.method === 'textDocument/publishDiagnostics') {
        this.emit('diagnostics', message.params);
      }
    }
  }
}
