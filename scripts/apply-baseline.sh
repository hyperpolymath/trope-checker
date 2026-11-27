#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Apply .hypatia-baseline.json to a Hypatia findings file.
# Usage: apply-baseline.sh <findings.json> <baseline.json> [advisory|enforce]
# UNVERIFIED: written from CI log evidence, not from the standards repo.
# Findings are a JSON array with .type (rule id) and .file (repo-relative).
# Baseline is {"entries":[{"rule","file","reason"}]}; every entry needs a reason.
# Filtered findings go to stdout. In advisory mode, nothing is dropped.
set -euo pipefail
findings=${1:?findings file}; baseline=${2:?baseline file}; mode=${3:-enforce}
jq -e '.entries | type == "array" and all(.[]; (.rule|type=="string") and (.file|type=="string") and ((.reason // "")|length > 0))' \
  "$baseline" >/dev/null || { echo "::error::invalid baseline $baseline" >&2; exit 2; }
if [ "$mode" = advisory ]; then
  jq '.' "$findings"
else
  jq --slurpfile b "$baseline" \
    '[.[] | select(. as $f | ($b[0].entries | any(.rule == $f.type and .file == $f.file)) | not)]' "$findings"
fi
if [ -n "${GITHUB_ENV:-}" ]; then echo "HYPATIA_BASELINE_FILTERED=true" >> "$GITHUB_ENV"; fi
