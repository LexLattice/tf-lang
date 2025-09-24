import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname, resolve, isAbsolute } from 'node:path';

import { parseDSL } from './parser.mjs';

export async function readText(p) {
  return await readFile(p, 'utf8');
}

export async function writeText(p, s) {
  await mkdir(dirname(p), { recursive: true });
  await writeFile(p, s, 'utf8');
}

export async function expandIncludes(ir, options = {}) {
  const ctx = {
    base: options.base || process.cwd(),
    loadFile: options.loadFile || readText,
    parse: options.parse || parseDSL,
    stack: Array.isArray(options.stack) ? [...options.stack] : []
  };
  return await expandNode(ir, ctx);
}

async function expandNode(node, ctx) {
  if (!node || typeof node !== 'object') return node;

  if (node.node === 'Include') {
    return await expandInclude(node, ctx);
  }

  if (node.node === 'Let') {
    const init = node.init ? await expandNode(node.init, ctx) : node.init;
    const body = node.body ? await expandNode(node.body, ctx) : node.body;
    return { ...node, init, body };
  }

  if (node.node === 'Prim') {
    const args = await expandValue(node.args, ctx);
    return { ...node, args };
  }

  if (node.node === 'Seq' || node.node === 'Par' || node.node === 'Region') {
    const children = await expandChildren(node.children || [], ctx);
    return { ...node, children };
  }

  if (node.node === 'Ref') {
    return { ...node };
  }

  if (Array.isArray(node)) {
    return await Promise.all(node.map((item) => expandNode(item, ctx)));
  }

  return await expandValue(node, ctx);
}

async function expandChildren(children, ctx) {
  const out = [];
  for (const child of children) {
    out.push(await expandNode(child, ctx));
  }
  return out;
}

async function expandValue(value, ctx) {
  if (!value || typeof value !== 'object') return value;
  if (Array.isArray(value)) {
    return Promise.all(value.map((item) => expandValue(item, ctx)));
  }
  if (value.node) {
    return await expandNode(value, ctx);
  }
  const out = {};
  for (const [key, val] of Object.entries(value)) {
    out[key] = await expandValue(val, ctx);
  }
  return out;
}

async function expandInclude(node, ctx) {
  const rel = typeof node.path === 'string' ? node.path : '';
  if (!rel) {
    throw new Error('IncludeNotFound: <empty path>');
  }
  const abs = isAbsolute(rel) ? rel : resolve(ctx.base, rel);
  if (ctx.stack.includes(abs)) {
    const chain = [...ctx.stack, abs].join(' -> ');
    throw new Error(`IncludeCycle: ${chain}`);
  }

  let text;
  try {
    text = await ctx.loadFile(abs);
  } catch (err) {
    if (err && err.code === 'ENOENT') {
      throw new Error(`IncludeNotFound: ${abs}`);
    }
    throw new Error(`IncludeError: ${abs}`);
  }

  const parseFn = ctx.parse || parseDSL;
  const childIr = parseFn(text);
  return await expandIncludes(childIr, {
    base: dirname(abs),
    loadFile: ctx.loadFile,
    parse: ctx.parse,
    stack: [...ctx.stack, abs]
  });
}
