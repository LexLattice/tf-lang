#!/usr/bin/env python3
import json
import sys
import os
import pathlib

OUT_ROOT = pathlib.Path(os.environ.get("OUT_ROOT", "out/t3"))
progress = OUT_ROOT / "_progress.log"
pauses = OUT_ROOT / "_pauses.log"
out_json = OUT_ROOT / "_pause_summary.json"


def parse_epochs(path):
    epochs = []
    if path.exists():
        for line in path.read_text(errors="ignore").splitlines():
            # JSON lines with ts_epoch (our prelude format)
            try:
                j = json.loads(line)
                if isinstance(j, dict) and "ts_epoch" in j:
                    epochs.append(int(j["ts_epoch"]))
                    continue
            except Exception:
                pass
            # fallback: none (we no longer emit bracketed timestamps)
    return sorted(epochs)


def parse_pause_events(path):
    spans = []
    start = None
    if path.exists():
        for line in path.read_text(errors="ignore").splitlines():
            try:
                j = json.loads(line)
            except Exception:
                continue
            if j.get("event") == "pause_start":
                start = j.get("start_epoch")
            elif j.get("event") == "pause_end" and start is not None:
                spans.append((start, j.get("end_epoch"), j.get("duration_s")))
                start = None
    return spans


ev = parse_epochs(progress)
spans = parse_pause_events(pauses)

if not ev:
    print("No events found.", file=sys.stderr)
    out_json.write_text(
        json.dumps({"event_count": 0, "note": "no progress events"}, indent=2)
    )
    sys.exit(0)

wall = ev[-1] - ev[0]
total_pause = sum([d for (_, _, d) in spans]) if spans else 0
effective = max(0, wall - total_pause)
gaps = [b - a for a, b in zip(ev, ev[1:])]
summary = {
    "wall_time_s": wall,
    "effective_work_s": effective,
    "total_pause_s": total_pause,
    "max_single_pause_s": max([d for (_, _, d) in spans], default=0),
    "max_silence_from_progress_s": max(gaps) if gaps else 0,
    "pause_spans": [{"start": s, "end": e, "dur_s": d} for (s, e, d) in spans],
    "event_count": len(ev),
}
out_json.write_text(json.dumps(summary, indent=2))
print(json.dumps(summary, indent=2))
