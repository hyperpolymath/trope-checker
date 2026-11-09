#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# 🔴 GATE: the Proof Witness Grade record is well-formed, and every published
# grade is the DERIVED one.
#
# PROOF-POLICY 8.4 rule 2 says a grade is computed from the receipts and the 2.2
# records, and that "a grade written by hand that the receipts do not support is
# drift". This gate is what makes that enforceable here:
#
#   1. the ledger is valid I-JSON and canonical JCS (owner ruling D306);
#   2. the ledger asserts NO grade — a `pwg` key on a theorem is itself a failure,
#      because the only legitimate source of a grade is the derivation;
#   3. every leg's receipt reference resolves, and every receipt carries the
#      fields 8.2 requires, including a full 40-character commit;
#   4. every section 5 token and every 2.2 state comes from its closed vocabulary;
#   5. the table and census published in docs/status/PROOF-STATUS.adoc are
#      byte-identical to what scripts/pwg-derive.sh produces.
#
# Fails loudly and says which rule broke. Usage: pwg-check.sh [REPO_ROOT]
set -uo pipefail

ROOT="${1:-$(cd "$(dirname "$0")/.." && pwd)}"
LEDGER="$ROOT/verification/pwg.json"
STATUS="$ROOT/docs/status/PROOF-STATUS.adoc"
DERIVE="$ROOT/scripts/pwg-derive.sh"
fail=0
die() { echo "::error::pwg-check: $*"; fail=1; }

command -v jq >/dev/null || { echo "::error::pwg-check: jq is required"; exit 2; }
[ -f "$LEDGER" ] || { echo "::error::pwg-check: no ledger at verification/pwg.json"; exit 1; }
[ -x "$DERIVE" ] || { echo "::error::pwg-check: scripts/pwg-derive.sh is missing or not executable"; exit 1; }

# --- 1. valid I-JSON, canonical JCS ---------------------------------------
if ! jq -e . "$LEDGER" >/dev/null 2>&1; then
  die "verification/pwg.json is not valid JSON"
else
  if ! jq -cS . "$LEDGER" | cmp -s - "$LEDGER"; then
    die "verification/pwg.json is not canonical JCS (owner ruling D306). Rewrite with: jq -cS . verification/pwg.json"
  fi
fi
if LC_ALL=C grep -qP '[\x00-\x08\x0b\x0c\x0e-\x1f]' "$LEDGER" 2>/dev/null; then
  die "verification/pwg.json contains control characters"
fi

# --- 2. the ledger must assert no grade -----------------------------------
# A grade in the evidence file is drift by construction: it could only have been
# written by hand, since the derivation lives in pwg-derive.sh.
asserted=$(jq -r '[.theorems[] | select(has("pwg") or has("grade") or has("PWG"))] | length' "$LEDGER" 2>/dev/null || echo 0)
if [ "${asserted:-0}" -gt 0 ]; then
  die "$asserted theorem record(s) in the ledger assert a grade. The ledger carries EVIDENCE only; grades are derived (PROOF-POLICY 8.4 rule 2). Remove the pwg/grade keys."
fi

# --- 3. receipt references resolve, and receipts are complete -------------
missing=$(jq -r '
  .receipts as $R
  | [ .theorems[] as $t
      | ($t.legs | to_entries[]) as $e
      | ($e.value.receipts // [])[]
      | select(($R[.] // null) == null)
      | "\($t.id)/\($e.key) -> \(.)" ]
  | .[]' "$LEDGER")
[ -n "$missing" ] && die "unresolved receipt reference(s):"$'\n'"$missing"

badr=$(jq -r '
  .receipts | to_entries[]
  | .key as $k | .value as $v
  | [ (if ($v.commit // "" | test("^[0-9a-f]{40}$")) then empty else "\($k): commit is not a full 40-char sha" end),
      (if ($v.checker // "" | length) > 0 then empty else "\($k): no checker" end),
      (if ($v.checker_version // "" | length) > 0 then empty else "\($k): no checker_version (8.2)" end),
      (if ($v.invocation // "" | length) > 0 then empty else "\($k): no invocation (8.2)" end),
      (if ($v.inputs_digest // "" | length) > 0 then empty else "\($k): no inputs_digest (8.2)" end),
      (if ($v.result // "" | length) > 0 then empty else "\($k): no result (8.2)" end),
      (if ($v.evidence // "" | length) > 0 then empty else "\($k): no evidence pointer" end),
      (if ($v.state // "" | test("^(current|superseded|regressed)$")) then empty else "\($k): state must be current|superseded|regressed (8.4 rule 5)" end),
      (if ($v | has("axioms")) then empty else "\($k): no axioms list (8.4 rule 6 — axioms travel with the grade)" end) ]
  | .[]' "$LEDGER")
[ -n "$badr" ] && die "incomplete receipt(s):"$'\n'"$badr"

# --- 4. closed vocabularies ----------------------------------------------
# Section 5 tokens, and the 2.2 correspondence states, plus the non-leg marker
# this repository uses for an engineering restatement.
badtok=$(jq -r '
  [ .theorems[] as $t
    | ($t.legs | to_entries[])
    | select((.value.token // "") | test("^(PROVEN|PROVEN-WITH-AXIOMS|TESTED|ASSUMED|OPEN)$") | not)
    | "\($t.id)/\(.key): token \(.value.token)" ]
  | .[]' "$LEDGER")
[ -n "$badtok" ] && die "token(s) outside the section 5 closed vocabulary:"$'\n'"$badtok"

badstate=$(jq -r '
  [ .theorems[] as $t
    | ($t.legs | to_entries[])
    | select((.value.state // "") | test("^(AGDA-PENDING|AGDA-VERIFIED|COQ-CHECKED|LEAN-CHECKED|BRIDGE-PENDING|RECONCILED|COUNTEREXAMPLE|QUARANTINED|NOT-INVENTORIED)$") | not)
    | "\($t.id)/\(.key): state \(.value.state)" ]
  | .[]' "$LEDGER")
[ -n "$badstate" ] && die "2.2 correspondence state(s) outside the closed vocabulary:"$'\n'"$badstate"

badroute=$(jq -r '
  [ .theorems[] as $t
    | ($t.legs | to_entries[])
    | select((.value.route // "") | test("^(transported|re-proved|waived|unavailable)$") | not)
    | "\($t.id)/\(.key): route \(.value.route)" ]
  | .[]' "$LEDGER")
[ -n "$badroute" ] && die "leg route(s) outside the 8.5 vocabulary:"$'\n'"$badroute"

# --- 5. the published table and census are the derived ones ---------------
if [ -f "$STATUS" ]; then
  want_table=$(bash "$DERIVE" --ledger "$LEDGER" --table) || die "pwg-derive --table failed"
  want_census=$(bash "$DERIVE" --ledger "$LEDGER" --census) || die "pwg-derive --census failed"
  got_table=$(awk '/^\/\/ PWG-TABLE:BEGIN/{f=1;next} /^\/\/ PWG-TABLE:END/{f=0} f' "$STATUS")
  if [ -z "$got_table" ]; then
    die "docs/status/PROOF-STATUS.adoc has no PWG-TABLE:BEGIN/END region to compare"
  elif [ "$got_table" != "$want_table" ]; then
    die "the PWG table in docs/status/PROOF-STATUS.adoc is not the derived one. Regenerate with: just pwg-render"
    diff <(printf '%s\n' "$got_table") <(printf '%s\n' "$want_table") | head -20 >&2 || true
  fi
  if ! grep -qF "$want_census" "$STATUS"; then
    die "the census line in docs/status/PROOF-STATUS.adoc is not the derived one. Expected:"$'\n'"$want_census"
  fi
fi

if [ "$fail" -eq 0 ]; then
  n=$(jq '.theorems | length' "$LEDGER")
  echo "PASS: PWG ledger well-formed, no asserted grades, $n obligation(s) derived, published table and census match"
fi
exit "$fail"
