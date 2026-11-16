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
#      byte-identical to what scripts/pwg-derive.sh produces;
#   6. every agda and lean witness name the ledger cites resolves to a
#      declaration in the sources (scripts/pwg-names.sh).
#
# Fails loudly and says which rule broke. Usage: pwg-check.sh [REPO_ROOT]
set -uo pipefail

ROOT="${1:-$(cd "$(dirname "$0")/.." && pwd)}"
LEDGER="$ROOT/verification/pwg.json"
STATUS="$ROOT/docs/status/PROOF-STATUS.adoc"
DERIVE="$ROOT/scripts/pwg-derive.sh"
fail=0
# Report the message arguments on stdout and mark the gate as failed without
# exiting, so subsequent checks can report further failures.
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
# Not `grep -qP`: -P is a build option, and `2>/dev/null` turned a grep that
# cannot do -P into a silent pass. `tr -d` of every allowed byte leaves exactly
# the disallowed ones, and is POSIX.
if [ "$(LC_ALL=C tr -d '\011\012\015\040-\377' < "$LEDGER" | wc -c)" -gt 0 ]; then
  die "verification/pwg.json contains control characters (I-JSON, RFC 7493)"
fi

# --- 2. the ledger must assert no grade -----------------------------------
# A grade in the evidence file is drift by construction: it could only have been
# written by hand, since the derivation lives in pwg-derive.sh.
# `2>/dev/null || echo 0` read "this ledger has no parseable .theorems" as "no
# asserted grades" — a malformed ledger passed rule 2 by being malformed.
asserted=$(jq -r '[.theorems[] | select(has("pwg") or has("grade") or has("PWG"))] | length' "$LEDGER") \
  || die "rule 2 could not be evaluated: the ledger has no well-formed .theorems array"
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
  | .[]' "$LEDGER") || die "rule 3 (receipt references) could not be evaluated: malformed theorem/leg shape"
[ -n "$missing" ] && die "unresolved receipt reference(s):"$'\n'"$missing"

badr=$(jq -r '
  .receipts | to_entries[]
  | .key as $k | .value as $v
  | [ (if ($v.commit // "" | test("\\A[0-9a-f]{40}\\z")) then empty else "\($k): commit is not a full 40-char sha" end),
      (if ($v.checker // "" | length) > 0 then empty else "\($k): no checker" end),
      (if ($v.checker_version // "" | length) > 0 then empty else "\($k): no checker_version (8.2)" end),
      (if ($v.invocation // "" | length) > 0 then empty else "\($k): no invocation (8.2)" end),
      (if ($v.inputs_digest // "" | length) > 0 then empty else "\($k): no inputs_digest (8.2)" end),
      (if ($v.result == "pass" or $v.result == "fail") then empty else "\($k): result must be pass|fail (8.2 -- the derivation reads it; an unrecognised value must not be treated as a pass)" end),
      (if ($v.evidence // "" | length) > 0 then empty else "\($k): no evidence pointer" end),
      (if ($v.state // "" | test("\\A(current|superseded|regressed)\\z")) then empty else "\($k): state must be current|superseded|regressed (8.4 rule 5)" end),
      (if ($v | has("axioms")) then empty else "\($k): no axioms list (8.4 rule 6 — axioms travel with the grade)" end) ]
  | .[]' "$LEDGER") \
  || die "rule 3 (receipt completeness) could not be evaluated over this ledger: malformed theorem/leg/receipt shape"
[ -n "$badr" ] && die "incomplete receipt(s):"$'\n'"$badr"

# --- 4. closed vocabularies ----------------------------------------------
# Section 5 tokens, and the 2.2 correspondence states, plus the non-leg marker
# this repository uses for an engineering restatement.
badtok=$(jq -r '
  [ .theorems[] as $t
    | ($t.legs | to_entries[])
    | select((.value.token // "") | test("\\A(PROVEN|PROVEN-WITH-AXIOMS|TESTED|ASSUMED|OPEN)\\z") | not)
    | "\($t.id)/\(.key): token \(.value.token)" ]
  | .[]' "$LEDGER") \
  || die "rule 4 (section 5 tokens) could not be evaluated over this ledger: malformed theorem/leg/receipt shape"
[ -n "$badtok" ] && die "token(s) outside the section 5 closed vocabulary:"$'\n'"$badtok"

badstate=$(jq -r '
  [ .theorems[] as $t
    | ($t.legs | to_entries[])
    | select((.value.state // "") | test("\\A(AGDA-PENDING|AGDA-VERIFIED|COQ-CHECKED|LEAN-CHECKED|BRIDGE-PENDING|RECONCILED|COUNTEREXAMPLE|QUARANTINED|NOT-INVENTORIED)\\z") | not)
    | "\($t.id)/\(.key): state \(.value.state)" ]
  | .[]' "$LEDGER") \
  || die "rule 4 (2.2 states) could not be evaluated over this ledger: malformed theorem/leg/receipt shape"
[ -n "$badstate" ] && die "2.2 correspondence state(s) outside the closed vocabulary:"$'\n'"$badstate"

badroute=$(jq -r '
  [ .theorems[] as $t
    | ($t.legs | to_entries[])
    | select((.value.route // "") | test("\\A(transported|re-proved|waived|unavailable)\\z") | not)
    | "\($t.id)/\(.key): route \(.value.route)" ]
  | .[]' "$LEDGER") \
  || die "rule 4 (8.5 routes) could not be evaluated over this ledger: malformed theorem/leg/receipt shape"
[ -n "$badroute" ] && die "leg route(s) outside the 8.5 vocabulary:"$'\n'"$badroute"

# --- 5. the published table and census are the derived ones ---------------
# A missing status file used to skip rule 5 silently and still print "published
# table and census match". Renaming the file was therefore enough to forge every
# grade in it and pass the gate.
if [ ! -f "$STATUS" ]; then
  die "no published status file at docs/status/PROOF-STATUS.adoc — rule 5 cannot be checked. A deleted or moved status file is drift, not a pass."
else
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

# --- 6. every cited witness names a declaration that exists ----------------
# Measured 2026-11-16 against main 0dceab6: 13 of the ledger's 91 distinct
# witness names resolved to nothing in the sources -- ASCII transliterations
# (`|>` for `▷`, `beta-` for `β-`), a kebab-case spelling of a camelCase name, a
# lemma split in two (`gmonoid-unit` vs `gmonoid-unitL`/`-unitR`), a wrong Lean
# namespace -- including L2's ONLY Agda witness, on a row published PWG-3. The
# grade was derived from tokens and receipts; nothing checked that the token's
# witness existed. scripts/pwg-names.sh inventories the declared names; this rule
# resolves every agda and lean leg's `declarations` against it. Agda names must
# match exactly (a module name is also a valid citation); a Lean name may omit a
# leading namespace prefix, so it resolves if some declaration equals it or ends
# with `.<name>`. Name resolution, not proof: the receipt still carries that.
NAMES="$ROOT/scripts/pwg-names.sh"
if [ ! -f "$NAMES" ]; then
  die "scripts/pwg-names.sh is missing -- rule 6 (witness names resolve) cannot be checked"
elif ! inventory=$(bash "$NAMES" "$ROOT" 2>&1); then
  die "rule 6 could not build the declaration inventory:"$'\n'"$inventory"
else
  dangling=$(jq -r '
      .theorems[] as $t
      | ($t.legs | to_entries[]) | select(.key == "agda" or .key == "lean")
      | .key as $l | (.value.declarations // [])[]
      # Lossless: each field is JSON-escaped (quotes dropped), so a tab or
      # newline inside a citation stays INSIDE its field as a visible \t / \n
      # and the name then matches nothing. Interpolating raw let a citation
      # with "\tjunk" appended split into an extra field the resolver ignored,
      # and the original name resolved. Ordinary names, Unicode included,
      # come through @json unchanged.
      | [$l, $t.id, .] | map(@json | .[1:-1]) | join("\t")' "$LEDGER" \
    | INV="$inventory" awk -F'\t' '
        BEGIN {
          n = split(ENVIRON["INV"], rows, "\n")
          for (i = 1; i <= n; i++) { split(rows[i], f, "\t"); have[f[1] "\t" f[2]] = 1; if (f[1] == "lean") lean[++ln] = f[2] }
        }
        NF != 3 { print "malformed citation record: " $0; next }
        {
          ok = (($1 "\t" $3) in have)
          if (!ok && $1 == "lean")
            for (i = 1; i <= ln && !ok; i++) {
              L = lean[i]; m = length($3)
              if (length(L) > m && substr(L, length(L) - m) == "." $3) ok = 1
            }
          if (!ok) print $2 "/" $1 ": " $3
        }') || die "rule 6 (witness names resolve) could not be evaluated over this ledger"
  [ -n "$dangling" ] && die "witness name(s) that resolve to no declaration in the sources:"$'\n'"$dangling"
fi

if [ "$fail" -eq 0 ]; then
  n=$(jq -e '.theorems | length' "$LEDGER") || die "the ledger has no .theorems array"
  echo "PASS: PWG ledger well-formed, no asserted grades, every witness name resolves, $n obligation(s) derived, published table and census match"
fi
exit "$fail"
