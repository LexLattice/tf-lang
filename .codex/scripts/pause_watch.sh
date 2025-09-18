#!/usr/bin/env bash
set -euo pipefail
LOG="out/t1/_progress.log"
PAUSELOG="out/t1/_pauses.log"
THRESH=${1:-90}
mkdir -p out/t1; touch "$LOG" "$PAUSELOG"
in_pause=0; pause_start=0
while true; do
  sleep 5
  new_mtime=$(stat -c %Y "$LOG" 2>/dev/null || date +%s)
  now=$(date +%s); delta=$(( now - new_mtime ))
  if (( delta > THRESH )); then
    if (( in_pause == 0 )); then
      in_pause=1; pause_start=$(( new_mtime + THRESH ))
      printf '{"event":"pause_start","ts":"%s","start_epoch":%s,"since_log_epoch":%s,"threshold_s":%s}\n' \
        "$(date -Iseconds)" "$pause_start" "$new_mtime" "$THRESH" >> "$PAUSELOG"
    fi
  else
    if (( in_pause == 1 )); then
      in_pause=0; dur=$(( now - pause_start )); ((dur<0)) && dur=0
      printf '{"event":"pause_end","ts":"%s","end_epoch":%s,"duration_s":%s}\n' \
        "$(date -Iseconds)" "$now" "$dur" >> "$PAUSELOG"
    fi
  fi
done
