#!/usr/bin/env python3
import os

ROOT = ".codex/tasks"
INDEX = ".codex/tasks/INDEX.md"


def first_bullets(path, max_bullets=3):
    bullets = []
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            if line.strip().startswith("- "):
                bullets.append(line.strip()[2:].strip())
                if len(bullets) >= max_bullets:
                    break
    return bullets


def main():
    sections = []
    for task in sorted(
        d for d in os.listdir(ROOT) if os.path.isdir(os.path.join(ROOT, d))
    ):
        eg = os.path.join(ROOT, task, "END_GOAL.md")
        if not os.path.isfile(eg):
            continue
        bullets = first_bullets(eg)
        bullet_md = (
            "\n".join(f"  - {b}" for b in bullets)
            if bullets
            else "  - (no bullets found)"
        )
        sections.append(f"## {task}\n{bullet_md}\n")
    content = "# Task Index\n\n" + "\n".join(sections)
    os.makedirs(os.path.dirname(INDEX), exist_ok=True)
    with open(INDEX, "w", encoding="utf-8") as f:
        f.write(content)
    print(f"[briefs-index] wrote {INDEX}")


if __name__ == "__main__":
    main()
