#!/usr/bin/env bash
set -euo pipefail
WATCH_DIR="${1:-$PWD}"
LOG="out/t1/_fs.log"; mkdir -p out/t1
IGNORE_REGEX='(^|/)(\.git|node_modules|target|dist|.pnpm|.pnpm-store|out/t1/_.*)($|/)'

if command -v inotifywait >/dev/null 2>&1; then
  EVENTS="${FS_EVENTS:-create,modify,delete,move,close_write}"
  inotifywait -m -r -e "$EVENTS" --timefmt '%s' --format '%T|%e|%w|%f' "$WATCH_DIR" \
  | awk -v IGN="$IGNORE_REGEX" -F'|' '
    function esc(s){gsub(/\\/,"\\\\",s);gsub(/"/,"\\\"",s);return s}
    { path=$3 $4; if (path ~ IGN) next;
      n=split($2,evs,","); for (i=1;i<=n;i++)
        printf("{\"event\":\"fs_%s\",\"ts_epoch\":%s,\"path\":\"%s\"}\n", tolower(evs[i]), $1, esc(path));
      fflush(stdout);
    }' >> "$LOG"
else
  # macOS fallback
  if command -v fswatch >/dev/null 2>&1; then
    fswatch -r "$WATCH_DIR" \
    | while IFS= read -r p; do
        [[ "$p" =~ $IGNORE_REGEX ]] && continue
        printf '{"event":"fs_touch","ts_epoch":%s,"path":%s}\n' "$(date +%s)" "$(jq -Rn --arg s "$p" '$s')" >> "$LOG"
      done
  fi
fi
