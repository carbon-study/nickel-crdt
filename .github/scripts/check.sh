#!/usr/bin/env bash
# Usage: check.sh NAME SECONDS COMMAND...
# Runs COMMAND with a time limit. On failure, the last 60 lines of its output
# become an ::error:: annotation, which is readable through the API (Actions
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
tail -n 60 "$log" | sed 's/%/%25/g' | awk '{printf "%s%%0A", $0}' | sed "s/^/::error title=$name::/"
echo
exit "$status"
