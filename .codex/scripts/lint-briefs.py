#!/usr/bin/env python3
import sys
import os
import yaml

ROOT = ".codex/tasks"


def err(msg):
    print(f"[briefs-lint] {msg}")
    return 1


def main():
    if not os.path.isdir(ROOT):
        return err(f"missing {ROOT}")
    bad = 0
    for task in sorted(
        d for d in os.listdir(ROOT) if os.path.isdir(os.path.join(ROOT, d))
    ):
        base = os.path.join(ROOT, task)
        eg = os.path.join(base, "END_GOAL.md")
        bl = os.path.join(base, "BLOCKERS.yml")
        ac = os.path.join(base, "ACCEPTANCE.md")
        missing = [p for p in (eg, bl, ac) if not os.path.isfile(p)]
        if missing:
            print(
                f"✗ {task}: missing {', '.join(os.path.basename(m) for m in missing)}"
            )
            bad += 1
            continue
        # Parse BLOCKERS
        try:
            with open(bl, "r", encoding="utf-8") as f:
                data = yaml.safe_load(f)
            if not isinstance(data, list) and not isinstance(data, dict):
                print(f"✗ {task}: BLOCKERS.yml should be a list or a map of rules")
                bad += 1
            elif isinstance(data, list) and not all(isinstance(x, str) for x in data):
                print(f"✗ {task}: BLOCKERS.yml list items must be strings")
                bad += 1
        except Exception as e:
            print(f"✗ {task}: BLOCKERS.yml parse error: {e}")
            bad += 1
            continue
        # Quick size hints (keep files ~1 page)
        for p in (eg, ac):
            lines = sum(1 for _ in open(p, "r", encoding="utf-8"))
            if lines > 200:
                print(
                    f"⚠ {task}: {os.path.basename(p)} is {lines} lines (consider tightening)"
                )
        print(f"✓ {task}: OK")
    if bad:
        sys.exit(1)
    print("[briefs-lint] all good")


if __name__ == "__main__":
    main()
