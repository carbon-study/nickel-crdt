#!/usr/bin/env bash
# Controls for check.sh: each case must finish within its bound and report the
# right status and annotation. Runs in a few seconds; CI runs it first.
set -u
here=$(dirname "$0"); fails=0
# Every long sleep below uses this run-unique duration, so the leftover check
# matches only processes this self-test started, never another job's sleep.
export nap="30.$$"
run() { # NAME LIMIT BOUND EXPECT_STATUS EXPECT_TEXT COMMAND...
  local name=$1 limit=$2 bound=$3 want=$4 text=$5; shift 5
  local start=$SECONDS out status
  out=$("$here/check.sh" "selftest-$name" "$limit" "$@" 2>&1); status=$?
  local took=$((SECONDS - start)) ok=1
  [ "$status" -eq "$want" ] || ok=0
  [ "$took" -le "$bound" ] || ok=0
  [ -z "$text" ] || grep -qF -- "$text" <<<"$out" || ok=0
  if [ $ok = 1 ]; then echo "ok   $name (exit $status, ${took}s)"
  else echo "FAIL $name: exit $status (want $want), ${took}s (bound ${bound}s)"; echo "$out" | tail -n 5; fails=$((fails+1)); fi
}
run pass      5  4 0   ""                              sh -c 'echo fine'
run fail      5  4 3   "::error title=selftest-fail::a%25b" sh -c 'echo a%b; exit 3'
run hang      1  4 124 "timed out after 1s"            sh -c 'exec sleep "$nap"'
# A child that ignores TERM: only the KILL 10s later ends it.
run ignore    1 14 124 "timed out after 1s"            bash -c 'trap "" TERM; sleep $nap & wait'
# Lynn's shape on #38: the command exits on TERM but leaves a TERM-ignoring
# descendant holding stdout open.
run orphan    1 14 124 "timed out after 1s"            bash -c 'bash -c "trap \"\" TERM; exec sleep $nap" & sleep $nap'
# The command finishes in time but leaves a descendant behind.
run leftover  5  4 0   ""                              bash -c 'sleep $nap & echo done'
pgrep -f "^sleep $nap$" > /dev/null && { echo "FAIL leftover processes:"; pgrep -af "^sleep $nap$"; fails=$((fails+1)); }
exit $((fails > 0))
