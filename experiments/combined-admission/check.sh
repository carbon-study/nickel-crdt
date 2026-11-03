#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
export PYTHONDONTWRITEBYTECODE=1
export NODE=$(command -v node)
mode=(); receipt="$here/receipt.json"; record=false
for arg in "$@"; do
  case "$arg" in
    --fugue) mode=(--fugue); receipt="$here/fugue-receipt.json";;
    --record) record=true;;
    *) echo "unknown argument: $arg" >&2; exit 2;;
  esac
done
nix develop "$root/experiments/hybrid-restoration" --command python "$root/experiments/order-effect-bridge/trace.py" > "$work/trace.json"
if ((${#mode[@]})); then
  BRIDGE_COLD=1 nix develop "$root/experiments/hybrid-restoration" --command python "$root/experiments/order-effect-bridge/trace.py" > "$work/cold.json"
  cmp "$work/trace.json" "$work/cold.json"
fi
nix develop "$root/experiments/hybrid-restoration" --command python "$here/check.py" "$work/trace.json" "${mode[@]}" > "$work/receipt.json"
if "$record"; then cp "$work/receipt.json" "$receipt"; else cmp "$work/receipt.json" "$receipt"; fi
controls=(receiver-visible-delete early-publish receiver-visible-gap duplicate-delete-target)
if ((${#mode[@]})); then controls+=(fugue-link-budget order-backend order-birth-count); fi
for control in "${controls[@]}"; do
  nix develop "$root/experiments/hybrid-restoration" --command python "$here/controls.py" "$work/trace.json" "$control" "${mode[@]}"
done
cat "$work/receipt.json"
