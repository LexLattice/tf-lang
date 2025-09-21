import { effectOf, effectRank, commuteSymmetric } from '../../tf-l0-check/src/effect-lattice.mjs';

export function normalizeByCommutation(ir, catalog = {}) {
  const { node } = visit(ir, catalog);
  return node;
}

function visit(node, catalog) {
  if (!node || typeof node !== 'object') {
    return { node, changed: false };
  }

  if (node.node === 'Seq') {
    const children = Array.isArray(node.children) ? node.children : [];
    let childChanged = false;
    const normalizedChildren = [];

    for (const child of children) {
      const result = visit(child, catalog);
      normalizedChildren.push(result.node);
      if (result.changed) {
        childChanged = true;
      }
    }

    const { nodes: reorderedChildren, changed: reorderChanged } = reorderSeq(normalizedChildren, catalog);

    if (!childChanged && !reorderChanged) {
      return { node, changed: false };
    }

    const finalChildren = reorderChanged ? reorderedChildren : normalizedChildren;
    return { node: { ...node, children: finalChildren }, changed: true };
  }

  if (node.node === 'Par' || node.node === 'Region') {
    const children = Array.isArray(node.children) ? node.children : [];
    let changed = false;
    const nextChildren = [];

    for (const child of children) {
      const result = visit(child, catalog);
      nextChildren.push(result.node);
      if (result.changed) {
        changed = true;
      }
    }

    if (!changed) {
      return { node, changed: false };
    }

    return { node: { ...node, children: nextChildren }, changed: true };
  }

  if (Array.isArray(node.children)) {
    let changed = false;
    const nextChildren = [];

    for (const child of node.children) {
      const result = visit(child, catalog);
      nextChildren.push(result.node);
      if (result.changed) {
        changed = true;
      }
    }

    if (!changed) {
      return { node, changed: false };
    }

    return { node: { ...node, children: nextChildren }, changed: true };
  }

  return { node, changed: false };
}

function reorderSeq(children, catalog) {
  if (!Array.isArray(children) || children.length < 2) {
    return { nodes: children, changed: false };
  }

  const nodes = children.slice();
  let changed = false;

  while (true) {
    let swapped = false;
    for (let i = 0; i < nodes.length - 1; i += 1) {
      const left = nodes[i];
      const right = nodes[i + 1];

      if (!isPrim(left) || !isPrim(right)) {
        continue;
      }

      const leftFamily = effectOf(left.prim, catalog);
      const rightFamily = effectOf(right.prim, catalog);

      if (!commuteSymmetric(leftFamily, rightFamily)) {
        continue;
      }

      const leftRank = effectRank(leftFamily);
      const rightRank = effectRank(rightFamily);

      if (!shouldSwap(left, right, leftRank, rightRank)) {
        continue;
      }

      nodes[i] = right;
      nodes[i + 1] = left;
      swapped = true;
      changed = true;
    }

    if (!swapped) {
      break;
    }
  }

  return { nodes: changed ? nodes : children, changed };
}

function shouldSwap(leftNode, rightNode, leftRank, rightRank) {
  if (rightRank < leftRank) {
    return true;
  }

  if (rightRank === leftRank) {
    return comparePrimIds(rightNode.prim, leftNode.prim) < 0;
  }

  return false;
}

function comparePrimIds(a, b) {
  return String(a ?? '').localeCompare(String(b ?? ''));
}

function isPrim(node) {
  return Boolean(node && node.node === 'Prim');
}
