import { createWriteStream, mkdirSync } from 'node:fs';
import path from 'node:path';

export type Sink = {
  write: (record: unknown) => Promise<void>;
  close: () => Promise<void>;
};

export async function openSink(targetPath: string): Promise<Sink> {
  if (targetPath === '-' || targetPath === '') {
    return {
      write: async (record: unknown) => {
        process.stdout.write(`${JSON.stringify(record)}\n`);
      },
      close: async () => {},
    };
  }
  const target = path.resolve(targetPath);
  mkdirSync(path.dirname(target), { recursive: true });
  const stream = createWriteStream(target, { flags: 'w' });
  await new Promise<void>((resolve, reject) => {
    stream.once('open', () => resolve());
    stream.once('error', reject);
  });
  return {
      write: (record: unknown) =>
      new Promise<void>((resolve, reject) => {
        stream.write(`${JSON.stringify(record)}\n`, (error: NodeJS.ErrnoException | null | undefined) => {
          if (error) reject(error);
          else resolve();
        });
      }),
    close: () =>
      new Promise<void>((resolve, reject) => {
        stream.end((error: NodeJS.ErrnoException | null | undefined) => {
          if (error) reject(error);
          else resolve();
        });
      }),
  };
}
