import { canonNumber } from '../../packages/pilot-core/dist/index.js';

function normalizeInput(value) {
  if (typeof value === 'number') {
    if (!Number.isFinite(value)) {
      throw new Error('decimal: non-finite number');
    }
    return canonNumber(value);
  }
  if (typeof value === 'string') {
    return canonNumber(value);
  }
  if (value && typeof value === 'object' && 'value' in value && 'scale' in value) {
    return value;
  }
  throw new Error(`decimal: unsupported input ${String(value)}`);
}

export function parseDecimal(input) {
  const source = normalizeInput(input);
  if (source && typeof source === 'object' && 'value' in source && 'scale' in source) {
    return { value: BigInt(source.value), scale: Number(source.scale) };
  }
  const canonical = String(source);
  const negative = canonical.startsWith('-');
  const body = negative ? canonical.slice(1) : canonical;
  const [intPartRaw, fracPartRaw = ''] = body.split('.', 2);
  const intPart = intPartRaw.length === 0 ? '0' : intPartRaw;
  const fracPart = fracPartRaw;
  const digits = `${intPart}${fracPart}`;
  const scale = fracPart.length;
  const bigintValue = BigInt(digits.length === 0 ? '0' : digits);
  return {
    value: negative ? -bigintValue : bigintValue,
    scale,
  };
}

export function zeroDecimal() {
  return { value: 0n, scale: 0 };
}

export function alignScale(decimal, targetScale) {
  if (!Number.isInteger(targetScale) || targetScale < 0) {
    throw new Error('decimal: target scale must be a non-negative integer');
  }
  const source = parseDecimal(decimal);
  if (source.scale === targetScale) {
    return { value: source.value, scale: targetScale };
  }
  if (source.scale < targetScale) {
    const factor = 10n ** BigInt(targetScale - source.scale);
    return { value: source.value * factor, scale: targetScale };
  }
  const factor = 10n ** BigInt(source.scale - targetScale);
  if (source.value % factor !== 0n) {
    throw new Error('decimal: cannot reduce scale without precision loss');
  }
  return { value: source.value / factor, scale: targetScale };
}

export function addDecimal(a, b) {
  const scale = Math.max(parseDecimal(a).scale, parseDecimal(b).scale);
  const lhs = alignScale(a, scale);
  const rhs = alignScale(b, scale);
  return { value: lhs.value + rhs.value, scale };
}

export function negateDecimal(decimal) {
  const { value, scale } = parseDecimal(decimal);
  return { value: -value, scale };
}

export function absDecimal(decimal) {
  const { value, scale } = parseDecimal(decimal);
  return { value: value < 0n ? -value : value, scale };
}

export function multiplyDecimal(a, b) {
  const lhs = parseDecimal(a);
  const rhs = parseDecimal(b);
  return { value: lhs.value * rhs.value, scale: lhs.scale + rhs.scale };
}

export function decimalToString(decimal) {
  const { value, scale } = parseDecimal(decimal);
  if (scale === 0) {
    return value.toString();
  }
  const negative = value < 0n;
  let digits = (negative ? -value : value).toString();
  while (digits.length <= scale) {
    digits = `0${digits}`;
  }
  const intPartRaw = digits.slice(0, digits.length - scale);
  const fracPartRaw = digits.slice(digits.length - scale);
  const intPart = intPartRaw.replace(/^0+(?=\d)/, '') || '0';
  const fracPart = fracPartRaw.replace(/0+$/, '');
  const body = fracPart.length > 0 ? `${intPart}.${fracPart}` : intPart;
  return negative ? `-${body}` : body;
}

export function decimalToNumber(decimal) {
  const { value, scale } = parseDecimal(decimal);
  return Number(value) / 10 ** scale;
}

export function compareDecimal(a, b) {
  const scale = Math.max(parseDecimal(a).scale, parseDecimal(b).scale);
  const lhs = alignScale(a, scale).value;
  const rhs = alignScale(b, scale).value;
  if (lhs === rhs) return 0;
  return lhs < rhs ? -1 : 1;
}

