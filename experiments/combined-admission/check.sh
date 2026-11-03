#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
export PYTHONDONTWRITEBYTECODE=1
export NODE=$(command -v node)
nix develop "$root/experiments/hybrid-restoration" --command python "$root/experiments/order-effect-bridge/trace.py" > "$work/trace.json"
nix develop "$root/experiments/hybrid-restoration" --command python "$here/check.py" "$work/trace.json" > "$work/receipt.json"
if [ "${1:-}" = --record ]; then cp "$work/receipt.json" "$here/receipt.json"; else cmp "$work/receipt.json" "$here/receipt.json"; fi
for mode in receiver-visible-delete early-publish; do
  nix develop "$root/experiments/hybrid-restoration" --command python "$here/controls.py" "$work/trace.json" "$mode"
done
cat "$work/receipt.json"
