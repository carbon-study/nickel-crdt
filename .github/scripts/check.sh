#!/usr/bin/env bash
# Usage: check.sh NAME SECONDS COMMAND...
# Runs COMMAND with a time limit. On failure, the end of its output (lines that
# look like errors first, within GitHub's 4096-character limit) becomes an
# ::error:: annotation, which is readable through the API (Actions
# log downloads are not). The limit turns a hang into an annotated failure
# instead of a cancelled job, which would run no failure handler at all.
#
# COMMAND runs in its own process group with output going to a file, not a
# pipe, so a leftover descendant holding stdout cannot keep this script
# waiting. At the limit the whole group gets TERM, then KILL 10s later; once
# COMMAND exits, any remaining member of the group is killed.
set -u
name=$1 limit=$2; shift 2
log=/tmp/$name.log marker=/tmp/$name.timed-out
: > "$log"; rm -f "$marker"

setsid "$@" > "$log" 2>&1 < /dev/null &
pid=$!
tail -n +1 -f --pid="$pid" "$log" &
tailer=$!
# The watchdog has its own process group, so stopping it is one signal to the
# group: killing only its sleep would let it go on to mark a timeout.
setsid bash -c 'sleep "$1"; touch "$3"; kill -TERM -- "-$2"; sleep 10; kill -KILL -- "-$2"' \
  watchdog "$limit" "$pid" "$marker" > /dev/null 2>&1 < /dev/null &
watchdog=$!

wait "$pid"; status=$?
kill -KILL -- "-$watchdog" 2>/dev/null
kill -KILL -- "-$pid" 2>/dev/null
wait "$tailer" 2>/dev/null

if [ -e "$marker" ]; then
  echo "$name: timed out after ${limit}s (exit $status)" | tee -a "$log"
  status=124
fi
[ "$status" -eq 0 ] && exit 0
# GitHub keeps only the first 4096 characters of an annotation. Long lines (F*
# prints ~900-character command lines) once pushed the actual error out of the
# 60-line tail, so build the message under that budget: up to 8 lines that look
# like errors first, then as much of the tail as fits, each line cut to 300.
awk -v name="$name" '
  function cut(s) { return length(s) > 300 ? substr(s, 1, 297) "..." : s }
  { line[NR] = cut($0); if (tolower($0) ~ /error|fail|assert|panic|fatal|exception/) hit[++h] = NR }
  END {
    errs = ""
    for (i = (h > 8 ? h - 7 : 1); i <= h; i++) errs = errs line[hit[i]] "\n"
    if (errs != "") errs = "lines matching error patterns:\n" errs "--- last lines:\n"
    room = 3800 - length(errs); tail = ""
    for (i = NR; i >= 1 && i > NR - 60; i--) {
      if (length(tail) + length(line[i]) + 1 > room) break
      tail = line[i] "\n" tail
    }
    msg = errs tail
    gsub(/%/, "%25", msg); gsub(/\r/, "%0D", msg); gsub(/\n/, "%0A", msg)
    printf "::error title=%s::%s\n", name, msg
  }' "$log"
exit "$status"
