#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# The machine conformance suite: every IR fixture -> expected verdict (+ witness),
# and every schema-invalid fixture -> validation-fault at a named coordinate.
# Drives the compiled Idris2 reference checker (src/idris2/build/exec/tropecheck).
# Pure bash + jq; no Python.
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
# Honour TROPECHECK_BIN so the corpus can drive an alternative checker (e.g. the
# Rust fast-core for cross-validation); fall back to the Idris2 reference binary.
BIN="${TROPECHECK_BIN:-$ROOT/src/idris2/build/exec/tropecheck}"
CASES="$ROOT/tests/conformance/cases.json"
FIX="$ROOT/tests/conformance/fixtures"
INV="$ROOT/tests/conformance/schema-invalid"
G="\033[32m"; R="\033[31m"; O="\033[0m"
fail=0

command -v jq >/dev/null || { echo "jq is required"; exit 2; }
[ -x "$BIN" ] || { echo "checker not built: run 'just trope-build' first ($BIN)"; exit 2; }

# 0. every fixture (and the schema) is well-formed JSON.
for f in "$FIX"/*.ir.json "$INV"/*.json "$ROOT/schemas/trope-ir.schema.json"; do
  jq -e . "$f" >/dev/null 2>&1 || { echo -e "${R}FAIL${O} malformed JSON: $f"; fail=1; }
done

# 1. positive conformance: verdict (+ witness/coordinate) must match cases.json.
while read -r c; do
  ir=$(jq -r '.ir' <<<"$c")
  exp=$(jq -r '.expect' <<<"$c")
  wexp=$(jq -r '.witness // ""' <<<"$c")
  cexp=$(jq -r '.witness_coordinate // ""' <<<"$c")
  out=$("$BIN" "$FIX/$ir")
  verdict=$(awk '{print $1}' <<<"$out")
  ok=1
  [ "$verdict" = "$exp" ] || ok=0
  if [ -n "$wexp" ]; then
    gw=$(grep -o 'witness=[^[:space:]]*' <<<"$out" | cut -d= -f2)
    gc=$(grep -o 'coord=[^[:space:]]*' <<<"$out" | cut -d= -f2)
    { [ "$gw" = "$wexp" ] && [ "$gc" = "$cexp" ]; } || ok=0
  fi
  if [ "$ok" = 1 ]; then echo -e "${G}ok${O}   $ir -> $verdict${wexp:+ (witness $wexp/$cexp)}"
  else echo -e "${R}FAIL${O} $ir: got '$out', expected $exp ${wexp:+$wexp/$cexp}"; fail=1; fi
done < <(jq -c '.cases[]' "$CASES")

# 2. negative: schema-invalid fixtures must be rejected at validation (exit 2).
for f in "$INV"/*.json; do
  out=$("$BIN" "$f"); rc=$?
  if [ "$rc" = 2 ]; then echo -e "${G}ok${O}   $(basename "$f") rejected: ${out#validation-fault$'\t'}"
  else echo -e "${R}FAIL${O} $(basename "$f"): expected validation-fault, got rc=$rc '$out'"; fail=1; fi
done

if [ "$fail" = 0 ]; then echo -e "\n${G}conformance: all pass${O}"; else echo -e "\n${R}conformance: failures${O}"; fi
exit "$fail"
