#!/usr/bin/env bash
set -euo pipefail

LOG="erdos107/logs/proof_poll.log"
SOLVER_LOG="erdos107/logs/cadical_6_17_lrat_nocongruence.log"
SOLVER_PAT="cadical .*--lrat=1 .*py_6_17.cnf .*py_6_17.lrat.pipe"
CHECK_PAT="cake_lpr .*py_6_17.cnf .*py_6_17.lrat.pipe"

while true; do
  ts="$(date '+%Y-%m-%d %H:%M:%S')"
  solver_pid="$(pgrep -f "$SOLVER_PAT" | head -n 1 || true)"
  check_pid="$(pgrep -f "$CHECK_PAT" | head -n 1 || true)"

  if [[ -n "$solver_pid" ]]; then
    solver_ps="$(ps -o pid=,etime=,rss=,%cpu= -p "$solver_pid" 2>/dev/null || true)"
  else
    solver_ps="not running"
  fi

  if [[ -n "$check_pid" ]]; then
    check_ps="$(ps -o pid=,etime=,rss=,%cpu= -p "$check_pid" 2>/dev/null || true)"
  else
    check_ps="not running"
  fi

  if [[ -f "$SOLVER_LOG" ]]; then
    last_line="$(awk '/^c /{line=$0} END{print line}' "$SOLVER_LOG")"
  else
    last_line="(solver log missing)"
  fi

  {
    echo "[$ts]"
    echo "solver: $solver_ps"
    echo "checker: $check_ps"
    echo "log: $last_line"
    echo
  } >> "$LOG"

  sleep 1800
done
