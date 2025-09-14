#!/usr/bin/env python3
import sys, re
from pathlib import Path

# Headers
RE_DIFF = re.compile(r"^diff --git a/(.+) b/\1$")
RE_IDX = re.compile(r"^index [0-9a-f]+\.\.[0-9a-f]+")
RE_OLD = re.compile(r"^--- a/(.+)$")
RE_NEW = re.compile(r"^\+\+\+ b/(.+)$")


def read_lines(p: Path):
    return p.read_text(encoding="utf-8", errors="replace").splitlines()


def strip_preamble(lines):
    # Keep from first diff/--- header; drop markdown fences
    start = 0
    for i, ln in enumerate(lines):
        if ln.startswith("diff --git") or ln.startswith("--- a/"):
            start = i
            break
    return [ln for ln in lines[start:] if not ln.startswith("```")]


def split_file_blocks(lines):
    """Yield (diff_hdr?, index_hdr?, old_hdr, new_hdr, hunks_lines) per file."""
    i, n = 0, len(lines)
    while i < n:
        # Seek file start
        while i < n and not (
            lines[i].startswith("diff --git") or lines[i].startswith("--- a/")
        ):
            i += 1
        if i >= n:
            break

        diff_hdr = lines[i] if lines[i].startswith("diff --git") else None
        if diff_hdr:
            i += 1

        idx_hdr = lines[i] if i < n and RE_IDX.match(lines[i]) else None
        if idx_hdr:
            i += 1

        if i >= n or not RE_OLD.match(lines[i]):
            break
        old_hdr = lines[i]
        i += 1
        if i >= n or not RE_NEW.match(lines[i]):
            break
        new_hdr = lines[i]
        i += 1

        # Collect until next file header
        start = i
        while i < n and not (
            lines[i].startswith("diff --git") or lines[i].startswith("--- a/")
        ):
            i += 1
        yield (diff_hdr, idx_hdr, old_hdr, new_hdr, lines[start:i])


def split_hunks(block):
    """Yield lists for each @@... hunk (including the @@ line)."""
    i, n = 0, len(block)
    while i < n:
        if not block[i].startswith("@@"):
            i += 1
            continue
        j = i + 1
        while j < n and not block[j].startswith("@@"):
            j += 1
        yield block[i:j]
        i = j


def build_anchor(body):
    """
    Prefer leading context (' ') lines; else use first few '-' lines.
    Returns list[str] (without diff prefix).
    """
    lead_ctx = []
    for L in body:
        if L and L[0] == " ":
            lead_ctx.append(L[1:])
        else:
            break
    if lead_ctx:
        return lead_ctx
    minus = [L[1:] for L in body if L and L[0] == "-"]
    return minus[: min(8, len(minus))]  # small window


def counts(body):
    oldc = newc = 0
    for L in body:
        if not L:
            continue
        t = L[0]
        if t == " ":
            oldc += 1
            newc += 1
        elif t == "-":
            oldc += 1
        elif t == "+":
            newc += 1
    return oldc, newc


def find_from(doc, pattern, start_hint):
    """
    Find pattern in doc at/after start_hint; if not found, search from 0.
    Returns index or -1.
    """
    if not pattern:
        return start_hint
    max_i = len(doc) - len(pattern)
    i = min(max(start_hint, 0), max_i)
    while i <= max_i:
        if doc[i : i + len(pattern)] == pattern:
            return i
        i += 1
    i = 0
    while i <= max_i:
        if doc[i : i + len(pattern)] == pattern:
            return i
        i += 1
    return -1


def main():
    if len(sys.argv) < 2:
        print("usage: repair_patch2.py BROKEN.patch [repo_root=.]", file=sys.stderr)
        sys.exit(2)
    patch = Path(sys.argv[1])
    repo = Path(sys.argv[2]) if len(sys.argv) > 2 else Path(".")

    raw = strip_preamble(read_lines(patch))
    out = []
    for diff_hdr, idx_hdr, old_hdr, new_hdr, block in split_file_blocks(raw):
        m_old = RE_OLD.match(old_hdr)
        m_new = RE_NEW.match(new_hdr)
        old_path, new_path = m_old.group(1), m_new.group(1)
        if old_path != new_path:
            sys.exit(
                f"Renames not supported in this simple reconstructor: {old_path} -> {new_path}"
            )

        file_path = repo / old_path
        if not file_path.exists():
            sys.exit(f"Source file missing: {old_path}")

        old_lines = read_lines(file_path)

        # Emit headers as-is (keep diff/index if present)
        if diff_hdr:
            out.append(diff_hdr)
        if idx_hdr:
            out.append(idx_hdr)
        out.append(old_hdr)
        out.append(new_hdr)

        line_shift = 0  # newStart = oldStart + line_shift
        cursor_hint = 0  # search begins after last hunk application

        for hunk in split_hunks(block):
            body = hunk[1:]  # skip '@@'
            oldc, newc = counts(body)
            anchor_pat = build_anchor(body)

            pos = find_from(old_lines, anchor_pat, cursor_hint)
            if pos < 0:
                # Fallback: try using the entire old body (minus '+') if our small anchor didn't match
                old_body_full = [L[1:] for L in body if L and L[0] in (" ", "-")]
                pos = find_from(old_lines, old_body_full, cursor_hint)
            if pos < 0:
                # As a last resort, place hunk at cursor_hint (good enough to generate numbers; git will fuzzy-match)
                pos = cursor_hint

            old_start = pos + 1
            new_start = old_start + line_shift

            # Emit reconstructed header and body
            out.append(f"@@ -{old_start},{oldc} +{new_start},{newc} @@")
            out.extend(body)

            # Advance search window: consume exactly oldc lines from old_lines starting at pos
            cursor_hint = pos + oldc
            line_shift += newc - oldc

    sys.stdout.write("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
