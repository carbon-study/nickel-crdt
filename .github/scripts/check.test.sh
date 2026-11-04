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
# F*-shaped failure: very long lines around the error must not push it out of
# the annotation, which GitHub truncates at 4096 characters.
export long='x=$(printf "%0900d" 0); for i in $(seq 80); do echo "$x"; done'
run long      5  4 1   "FATAL real error here"         bash -c 'eval "$long"; echo "FATAL real error here"; for i in 1 2 3; do echo "${x}"; done; exit 1'
# What survives is the first 4095 characters: the error must be inside them.
msg=$("$here/check.sh" selftest-size 5 bash -c 'eval "$long"; echo "FATAL real error here"; for i in 1 2 3; do echo "${x}"; done; exit 1' 2>&1 | grep '^::error' | sed 's/^::error title=selftest-size:://; s/%0A/\n/g; s/%25/%/g')
if [ "${#msg}" -lt 4096 ] && grep -qF "FATAL real error here" <<<"${msg:0:4095}"; then echo "ok   size (${#msg} chars, error kept)"
else echo "FAIL size: ${#msg} chars; error within first 4095: $(grep -cF "FATAL real error here" <<<"${msg:0:4095}")"; fails=$((fails+1)); fi
pgrep -f "^sleep $nap$" > /dev/null && { echo "FAIL leftover processes:"; pgrep -af "^sleep $nap$"; fails=$((fails+1)); }
exit $((fails > 0))
