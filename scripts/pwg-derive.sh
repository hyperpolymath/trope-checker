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
DERIVE='
  # A section 5 token that means the kernel accepted it.
  def accepted: . == "PROVEN" or . == "PROVEN-WITH-AXIOMS";

  # A receipt is usable when it is the current one and names a full 40-char commit
  # (8.2 PWG-1: "the source repository and its full 40-character commit").
  def usable_receipt($rs): $rs
    | map(select(.state == "current" and (.commit | test("^[0-9a-f]{40}$"))))
    | length > 0;

  # 8.2 PWG-3 additionally requires the receipt to record the checker version,
  # the standard-library pin, the flags actually in force, and the import cone (1.1).
  def pwg3_receipt($rs): $rs
    | map(select(
        .state == "current"
        and (.commit | test("^[0-9a-f]{40}$"))
        and (.checker_version // "" | length > 0)
        and (.stdlib_pin // "" | length > 0)
        and (.import_cone // "" | length > 0)
        and (.invocation // "" | test("--safe"))
        and (.invocation // "" | test("--without-K"))
        and (.invocation // "" | test("--cubical-compatible"))
      ))
    | length > 0;

  # 8.2: "A leg counts when the target kernel accepted it as PROVEN or
  # PROVEN-WITH-AXIOMS and its 2.2 correspondence state is RECONCILED." And:
  # a waived leg, an unavailable leg and any BRIDGE-PENDING leg do not count.
  def counts($leg; $receipts):
    ($leg.token | accepted)
    and $leg.state == "RECONCILED"
    and ($leg.route != "waived" and $leg.route != "unavailable")
    and usable_receipt([$leg.receipts[] | $receipts[.]]);

  .receipts as $R
  | .theorems
  | map(
      . as $t
      | ($t.legs.agda) as $a
      | ($t.legs.rocq) as $c
      | ($t.legs.lean) as $l
      | ([$a.receipts[] | $R[.]]) as $ar
      | (($a.token | accepted) and $a.state == "AGDA-VERIFIED" and pwg3_receipt($ar)) as $agda_ok
      | (if counts($c; $R) then 1 else 0 end) as $nc
      | (if counts($l; $R) then 1 else 0 end) as $nl
      | ($nc + $nl) as $legs
      | (
          if $t.kind != "theory" then "not-applicable"        # 8.1: PWG applies to theory only
          elif ($agda_ok | not) then "ungraded"               # 8.1
          elif $legs == 0 then "3"
          elif $legs == 1 then "2i"
          else
            (if (usable_receipt($ar)
                 and usable_receipt([$c.receipts[] | $R[.]])
                 and usable_receipt([$l.receipts[] | $R[.]]))
             then "1" else "2ii" end)
          end
        ) as $grade
      | {
          id: $t.id,
          title: $t.title,
          kind: $t.kind,
          pwg: $grade,
          # 8.3: a non-DTT witness is a TAG beside the grade, never a leg.
          foundation_diverse: (($t.foundation_diverse_witness // null) != null),
          counting_legs: $legs,
          agda_receipt_complete: $agda_ok,
          axioms: ([ $ar[]? | .axioms[]? ] | unique),
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
