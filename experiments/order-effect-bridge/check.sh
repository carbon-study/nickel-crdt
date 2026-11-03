#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
# Python belongs to the existing reference's locked environment; Node belongs to root.
nix develop "$root/experiments/hybrid-restoration" --command python "$here/trace.py" > "$work/warm.json"
BRIDGE_COLD=1 nix develop "$root/experiments/hybrid-restoration" --command python "$here/trace.py" > "$work/cold.json"
cmp "$work/warm.json" "$work/cold.json"
node "$here/check.mjs" "$work/warm.json" > "$work/receipt.json"
cmp "$work/receipt.json" "$here/receipt.json"
cat "$work/receipt.json"
