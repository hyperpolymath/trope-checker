#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Exercise the exact per-module report predicate used by the proof workflow.
set -euo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
filter=$(sed -n "s/.*jq -e -s '\([^']*\)'.*/\1/p" "$root/.github/workflows/proofs.yml")
[[ -n "$filter" ]] || { echo 'Missing per-module report predicate' >&2; exit 1; }
check() {
  local expected=$1 input=$2 status
  if printf '%s' "$input" | jq -e -s "$filter" >/dev/null 2>&1; then status=0; else status=1; fi
  [[ "$status" == "$expected" ]] || { echo "Unexpected report result for: $input" >&2; exit 1; }
}
check 1 ''
check 1 '{'
check 1 '[]'
check 1 '{}'
check 1 '{"audited":"1"}'
check 1 '{"audited":1} {"audited":2}'
check 0 '{"audited":0}'
check 0 '{"audited":10,"violations":[]}'
echo 'PASS: every module must produce exactly one object with numeric audited'
