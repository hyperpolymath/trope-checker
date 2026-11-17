#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# DERIVE each theorem's Proof Witness Grade from the evidence in
# verification/pwg.json, per PROOF-POLICY section 8.
#
# PROOF-POLICY 8.4 rule 2: "Grades are derived, not asserted. A grade is computed
# from the receipts and the 2.2 records. A grade written by hand that the receipts
# do not support is drift. A gate or a bot may recompute it at any time and
# reports the computed value."
#
# So the ledger carries EVIDENCE — legs, tokens, 2.2 states, receipts — and this
# script is the only thing that turns evidence into a grade. Nothing downstream
# may write a grade by hand; scripts/pwg-check.sh enforces that.
#
# Usage:
#   pwg-derive.sh [--ledger PATH] --json      derived grade per theorem, as JCS JSON
#   pwg-derive.sh [--ledger PATH] --table     the AsciiDoc table for PROOF-STATUS
#   pwg-derive.sh [--ledger PATH] --census    the section 8.4 rule 7 census line
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
LEDGER="$ROOT/verification/pwg.json"
MODE=""
while [ $# -gt 0 ]; do
  case "$1" in
    --ledger) LEDGER="$2"; shift 2 ;;
    --json|--table|--census) MODE="$1"; shift ;;
    *) echo "pwg-derive: unknown argument '$1'" >&2; exit 2 ;;
  esac
done
[ -n "$MODE" ] || { echo "pwg-derive: one of --json --table --census is required" >&2; exit 2; }
[ -f "$LEDGER" ] || { echo "pwg-derive: no ledger at $LEDGER" >&2; exit 2; }
command -v jq >/dev/null || { echo "pwg-derive: jq is required" >&2; exit 2; }

# ---------------------------------------------------------------------------
# The derivation, as one jq program. Every rule cites the policy clause it
# implements, so a reader can check the code against section 8 line by line.
# ---------------------------------------------------------------------------
# shellcheck disable=SC2016  # single quotes are REQUIRED: $a/$c/$l/$t/$R below are
# jq variables, and the shell must not expand them.
#
# CONSEQUENCE, and it has bitten twice: NO APOSTROPHE MAY APPEAR ANYWHERE INSIDE
# THIS BLOCK, comments included. One closes the string, and what follows is read
# as shell. Write "the receipt of the leg", never "the leg's receipt". The first
# occurrence here was a Unicode right-quote, which survived only because it is
# not an ASCII apostrophe; "fixing" SC1112 by swapping in a plain one broke the
# script. Reword instead.
DERIVE='
  # A section 5 token that means the kernel accepted it.
  def accepted: . == "PROVEN" or . == "PROVEN-WITH-AXIOMS";

  # A receipt is usable when it is the current one, RECORDS A PASS, and names a
  # full 40-char commit (8.2 PWG-1: "the source repository and its full
  # 40-character commit").
  #
  # The result check is load-bearing, not decorative. Measured 2026-11-16 against
  # main 0dceab6: flipping the Agda receipt of this ledger to "result": "fail" while
  # leaving "state": "current" left the census byte-identical -- 17 PWG-3 grades
  # published on a receipt that records the checker REJECTING the development --
  # and scripts/pwg-check.sh exited 0. A grade may not outlive the run that
  # earned it; a regressed run is 8.2 evidence of the opposite.
  def usable_receipt($rs): $rs
    | map(select(.state == "current" and .result == "pass" and (.commit | test("\\A[0-9a-f]{40}\\z"))))
    | length > 0;

  # 2.1: every Agda entrypoint in the recorded invocation is the canonical one.
  # The invocation may join several commands with ";". Each command that runs
  # agda must be exactly: agda, the three flags as whole words, and one module.
  # The earlier test searched the whole string for the three flag substrings,
  # so one canonical command vouched for a second command that carried none of
  # them, and any further option rode along unseen. Measured 2026-11-17: with
  # the second entrypoint reduced to "agda Smoke.agda" the census did not move.
  def canonical_agda:
    [ split(";")[] | [splits("[[:space:]]+")] | map(select(length > 0)) | select(length > 0 and .[0] == "agda") ]
    | length > 0
      and all(.[];
        (.[1:] | map(select(startswith("-"))) | sort) == ["--cubical-compatible", "--safe", "--without-K"]
        and (.[1:] | map(select(startswith("-") | not)) | length) == 1);

  # 8.4 rule 6 and 8.5.1: a witness whose current receipt reports an axiom
  # without disposition c does not count. Dispositions are recorded on the
  # receipt as axiom_dispositions {name: c|b|debt}; an axiom with none recorded
  # is not admissible (fail closed). A receipt reporting no axiom is admissible.
  def axioms_admissible($rs): $rs
    | map(select(.state == "current"))
    | all(.[]; . as $r | all(($r.axioms // [])[]; ($r.axiom_dispositions // {})[.] == "c"));

  # 8.2 PWG-3 additionally requires the receipt to record the checker version,
  # the standard-library pin, the flags actually in force, and the import cone (1.1).
  def pwg3_receipt($rs): $rs
    | map(select(
        .state == "current"
        and .result == "pass"
        and (.commit | test("\\A[0-9a-f]{40}\\z"))
        and (.checker_version // "" | length > 0)
        and (.stdlib_pin // "" | length > 0)
        and (.import_cone // "" | length > 0)
        and (.invocation // "" | canonical_agda)
      ))
    | length > 0;

  # 8.2: "A leg counts when the target kernel accepted it as PROVEN or
  # PROVEN-WITH-AXIOMS and its 2.2 correspondence state is RECONCILED." And:
  # a waived leg, an unavailable leg and any BRIDGE-PENDING leg do not count.
  # Also require at least one current receipt with a full 40-character commit,
  # resolving the receipt IDs of the leg through the supplied receipt map.
  def counts($leg; $receipts):
    ($leg.token | accepted)
    and $leg.state == "RECONCILED"
    and ($leg.route != "waived" and $leg.route != "unavailable")
    and usable_receipt([$leg.receipts[] | $receipts[.]])
    and axioms_admissible([$leg.receipts[] | $receipts[.]]);

  # 8.3: the tag needs a kernel-checked witness whose statement correspondence
  # is recorded as in 2.2. A witness is {token, state, receipts}; it earns the
  # tag on the same terms a leg counts. The earlier test was "the field is not
  # null", so any value at all -- a note, a plan -- published the tag.
  def diverse($w; $receipts):
    ($w | type) == "object"
    and (($w.token // "") | accepted)
    and $w.state == "RECONCILED"
    and (($w.receipts // []) | length > 0)
    and usable_receipt([$w.receipts[] | $receipts[.]])
    and axioms_admissible([$w.receipts[] | $receipts[.]]);

  # 8.2 PWG-1 / 8.5.2: a receipt DESCRIBES the source commit when its commit is
  # the source commit of the ledger. (8.5.2 also admits an echo chain to it; this
  # ledger records no echoes, so a receipt from any other commit does not
  # describe it -- the conservative reading, and it still counts toward 3/2i/2ii.)
  def describes($rs; $src): $rs
    | map(select(.state == "current" and .result == "pass" and .commit == $src))
    | length > 0;

  .commit as $src
  | .receipts as $R
  | .theorems
  | map(
      . as $t
      | ($t.legs.agda) as $a
      | ($t.legs.rocq) as $c
      | ($t.legs.lean) as $l
      | ([$a.receipts[] | $R[.]]) as $ar
      | (($a.token | accepted) and $a.state == "AGDA-VERIFIED" and pwg3_receipt($ar) and axioms_admissible($ar)) as $agda_ok
      | (if counts($c; $R) then 1 else 0 end) as $nc
      | (if counts($l; $R) then 1 else 0 end) as $nl
      | ($nc + $nl) as $legs
      | (
          if $t.kind != "theory" then "not-applicable"        # 8.1: PWG applies to theory only
          elif ($agda_ok | not) then "ungraded"               # 8.1
          elif $legs == 0 then "3"
          elif $legs == 1 then "2i"
          else
            # Both legs count, so every conjunct of usable_receipt already holds
            # for all three witnesses: testing it here (as this branch once did)
            # made "2ii" unreachable and granted PWG-1 on PWG-2ii evidence. The
            # rung above 2ii is about WHICH COMMIT the receipts describe.
            (if (describes($ar; $src)
                 and describes([$c.receipts[] | $R[.]]; $src)
                 and describes([$l.receipts[] | $R[.]]; $src))
             then "1" else "2ii" end)
          end
        ) as $grade
      | {
          id: $t.id,
          title: $t.title,
          kind: $t.kind,
          pwg: $grade,
          # 8.3: a non-DTT witness is a TAG beside the grade, never a leg.
          foundation_diverse: diverse($t.foundation_diverse_witness // null; $R),
          counting_legs: $legs,
          agda_receipt_complete: $agda_ok,
          # 8.4 rule 6: the axioms of EVERY witness the grade stands on, not of the
          # Agda leg alone. A counting Rocq or Lean leg used to contribute its
          # count and none of its axioms.
          axioms: ([ ($ar[]? | .axioms[]?),
                     (if counts($c; $R) then ($c.receipts[] | $R[.] | .axioms[]?) else empty end),
                     (if counts($l; $R) then ($l.receipts[] | $R[.] | .axioms[]?) else empty end) ] | unique),
          legs: {
            agda: {route: $a.route, token: $a.token, state: $a.state, counts: (counts($a; $R))},
            rocq: {route: $c.route, token: $c.token, state: $c.state, counts: (counts($c; $R))},
            lean: {route: $l.route, token: $l.token, state: $l.state, counts: (counts($l; $R))}
          },
          notes: ($t.notes // "")
        }
    )
'

DERIVED="$(jq -cS "$DERIVE" "$LEDGER")" || { echo "pwg-derive: derivation failed" >&2; exit 1; }

case "$MODE" in
  --json) printf '%s\n' "$DERIVED" ;;

  --census)
    # 8.4 rule 7: a count per grade WITH THE DENOMINATOR, naming ungraded and the
    # lower rungs on the same line. Never a percentage, an average or a score.
    printf '%s' "$DERIVED" | jq -r '
      [.[] | select(.kind == "theory")] as $th
      | ($th | length) as $d
      | "*Census* (PROOF-POLICY §8.4 rule 7, never a percentage): of \($d) theory obligations in this repository, "
        + "`PWG-3` \([$th[] | select(.pwg == "3")] | length), "
        + "`PWG-2i` \([$th[] | select(.pwg == "2i")] | length), "
        + "`PWG-2ii` \([$th[] | select(.pwg == "2ii")] | length), "
        + "`PWG-1` \([$th[] | select(.pwg == "1")] | length), "
        + "`ungraded` \([$th[] | select(.pwg == "ungraded")] | length). "
        + (([$th[] | select(.foundation_diverse)] | length) as $fd
           | if $fd == 0 then "No obligation here carries `+foundation-diverse` (§8.3)."
             else "\($fd) carry `+foundation-diverse` (§8.3)." end)'
    ;;

  --table)
    echo '// GENERATED by scripts/pwg-derive.sh --table from verification/pwg.json.'
    echo '// Do not hand-edit: scripts/pwg-check.sh re-derives and fails on drift.'
    echo '[cols="2,1,1,3",options="header"]'
    echo '|==='
    # shellcheck disable=SC2016  # a literal AsciiDoc header row; nothing to expand.
    echo '| Obligation | `pwg` | Counting legs | Agda · Rocq · Lean (route · §5 token · §2.2 state)'
    printf '%s' "$DERIVED" | jq -r '.[] |
      "\n| \(.title)\n| `\(.pwg)`\(if .foundation_diverse then " `+foundation-diverse`" else "" end)\n| \(if .kind != "theory" then "— (§8.1: not on the ladder)" else "\(.counting_legs) of 2" end)\n| "
      + ([.legs.agda, .legs.rocq, .legs.lean]
         | map("\(.route) · `\(.token)` · `\(.state)`") | join(" · "))'
    echo '|==='
    ;;
esac
