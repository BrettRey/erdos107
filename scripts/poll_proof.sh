#!/usr/bin/env bash
set -euo pipefail

LOG="erdos107/logs/proof_poll.log"
STATUS="erdos107/logs/proof_status_latest.txt"
ALERT="erdos107/logs/proof_alert.log"
SOLVER_LOG="erdos107/logs/cadical_6_17_lrat_nocongruence.log"
SOLVER_PAT="cadical .*--lrat=1 .*py_6_17.cnf .*py_6_17.lrat"
CHECK_PAT="cake_lpr .*py_6_17.cnf .*py_6_17.chk.pipe"
EXPECT_CHECKER="${EXPECT_CHECKER:-0}"
PROOF_LRAT="/tmp/py_6_17.lrat"
PROOF_ZST="/tmp/py_6_17.lrat.zst"
CHECK_LOG="erdos107/logs/cake_lpr_6_17_stream.log"

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

  proof_lrat="(missing)"
  if [[ -f "$PROOF_LRAT" ]]; then
    proof_lrat="$(ls -lh "$PROOF_LRAT" | awk '{print $5}')"
  fi
  proof_zst="(missing)"
  if [[ -f "$PROOF_ZST" ]]; then
    proof_zst="$(ls -lh "$PROOF_ZST" | awk '{print $5}')"
  fi

  disk_free="$(df -h /System/Volumes/Data | awk 'NR==2{print $4}')"

  {
    echo "[$ts]"
    echo "solver: $solver_ps"
    echo "checker: $check_ps"
    echo "log: $last_line"
    echo "proof.lrat: $proof_lrat"
    echo "proof.zst: $proof_zst"
    echo "disk free: $disk_free"
    echo
  } >> "$LOG"

  {
    echo "timestamp: $ts"
    echo "solver: $solver_ps"
    echo "checker: $check_ps"
    echo "log: $last_line"
    echo "proof.lrat: $proof_lrat"
    echo "proof.zst: $proof_zst"
    echo "disk free: $disk_free"
  } > "$STATUS"

  if [[ -z "$solver_pid" ]]; then
    echo "[$ts] ALERT: solver not running (solver='$solver_pid')" >> "$ALERT"
  fi
  if [[ "$EXPECT_CHECKER" -eq 1 && -z "$check_pid" ]]; then
    echo "[$ts] ALERT: checker not running (checker='$check_pid')" >> "$ALERT"
  fi

  if [[ "$EXPECT_CHECKER" -eq 1 && -f "$CHECK_LOG" ]]; then
    if tail -n 200 "$CHECK_LOG" | rg -q "heap space exhausted"; then
      echo "[$ts] ALERT: CakeML heap exhausted" >> "$ALERT"
    fi
  fi

  sleep 1800
done
