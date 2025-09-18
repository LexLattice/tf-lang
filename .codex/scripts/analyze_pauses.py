#!/usr/bin/env python3
import json
import re
import sys
import pathlib

progress = pathlib.Path("out/t1/_progress.log")
pauses = pathlib.Path("out/t1/_pauses.log")
out_json = pathlib.Path("out/t1/_pause_summary.json")
ts_re = re.compile(r"\[(\d{4}-\d{2}-\d{2}T[^]]+)\]\[(\d+)\]")


def parse_epochs(path):
    epochs = []
    if path.exists():
        for line in path.read_text().splitlines():
            m = ts_re.search(line)
            if m:
                epochs.append(int(m.group(2)))
                continue
            try:
                j = json.loads(line)
                if "ts_epoch" in j:
                    epochs.append(int(j["ts_epoch"]))
            except Exception:
                pass
    return sorted(epochs)


def parse_pause_events(path):
    spans = []
    start = None
    if path.exists():
        for line in path.read_text().splitlines():
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
    sys.exit(1)
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
