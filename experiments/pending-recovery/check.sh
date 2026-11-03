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
nix develop "$root/experiments/hybrid-restoration" --command python "$here/control.py" "$work/trace.json"
nix develop "$root/experiments/hybrid-restoration" --command python "$here/process_probe.py" save "$work/checkpoint.json"
nix develop "$root/experiments/hybrid-restoration" --command python "$here/process_probe.py" resume "$work/checkpoint.json" > "$work/process.json"
cmp "$work/process.json" "$here/process-receipt.json"
cat "$work/receipt.json" "$work/process.json"
