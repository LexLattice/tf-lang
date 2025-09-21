import test from "node:test";
import assert from "node:assert/strict";

import {
  any,
  array,
  bytes,
  object,
  option,
  refined,
  string,
  toJSON,
  canonicalStringify,
  unify
} from "../packages/tf-l0-types/src/types.mjs";

function assertDeterministic(left, right) {
  const first = unify(left, right);
  const second = unify(left, right);
  assert.deepStrictEqual(first, second, "unify results should be deterministic");
  if (first.ok) {
    const jsonFirst = canonicalStringify(toJSON(first.type));
    const jsonSecond = canonicalStringify(toJSON(second.type));
    assert.strictEqual(jsonFirst, jsonSecond, "canonical JSON should be stable");
  }
  return first;
}

function assertCommutative(left, right) {
  const forward = unify(left, right);
  const backward = unify(right, left);
  assert.deepStrictEqual(forward, backward, "unify should be commutative");
  return forward;
}

test("refined hash type is stable", () => {
  const digest = refined(string(), "digest_sha256");
  const commutative = assertCommutative(digest, digest);
  assert.ok(commutative.ok, "refined string hashes should unify");
  const deterministic = assertDeterministic(digest, digest);
  assert.ok(deterministic.ok, "deterministic unify should succeed");
});

test("option(string) merges", () => {
  const left = option(string());
  const right = option(string());
  const result = assertCommutative(left, right);
  assert.ok(result.ok, "option(string) should unify");
  const json = canonicalStringify(toJSON(result.type));
  const again = canonicalStringify(toJSON(assertDeterministic(left, right).type));
  assert.strictEqual(json, again, "option unify should be stable");
});

test("any unifies with structured types", () => {
  const payload = array(string());
  const result = unify(any(), payload);
  assert.ok(result.ok, "any should unify with arrays");
  const json = canonicalStringify(toJSON(result.type));
  const expected = canonicalStringify(toJSON(payload));
  assert.strictEqual(json, expected, "any should return the other type");
});

test("bytes and string stay distinct", () => {
  const verdict = unify(bytes(), string());
  assert.deepStrictEqual(verdict, { ok: false, reason: "kind_mismatch" });
});

test("object shapes require matching fields", () => {
  const base = object({ topic: string(), key: string() });
  const missing = object({ topic: string() });
  const verdict = unify(base, missing);
  assert.deepStrictEqual(verdict, { ok: false, reason: "shape_mismatch" });
});

test("refinement mismatch fails", () => {
  const refinedUri = refined(string(), "uri");
  const plain = string();
  const verdict = unify(refinedUri, plain);
  assert.deepStrictEqual(verdict, { ok: false, reason: "refinement_mismatch" });
});
