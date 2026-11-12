#!/usr/bin/env bash
# Assertion gates only. Candidate searches print results and are not CI verdicts.
set -euo pipefail
cd "$(dirname "$0")/.."
node experiments/register-candidates/verify-q.mjs
node experiments/register-candidates/adopted.mjs
node experiments/register-candidates/check-claims.mjs
node experiments/collection-candidates/verify-k.mjs
node experiments/collection-candidates/adopted.mjs
