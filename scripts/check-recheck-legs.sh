#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# check-recheck-legs.sh rocq|lean|controls
#
# The gate for the PROOF-POLICY §2 recheck legs of the ratified-carrier order
# laws and L4 (verification/proofs/rocq/RatifiedOrder.v and
# verification/proofs/lean4/ratified-order/RatifiedOrder.lean). The same
# script runs locally and in CI (.github/workflows/proofs.yml), so a green
# local run and a green CI run mean the same thing.
#
#   rocq      coqc must be the pinned version; the file must compile; and
#             `Print Assumptions` must report "Closed under the global
#             context" for EVERY Theorem and Lemma the file declares.
#   lean      lean must be the pinned version; the file must check with no
#             error and no warning (a `sorry` only warns); and EVERY theorem
#             the source declares must depend on no axiom at all
#             (Lean.collectAxioms, the function behind #print axioms).
#   controls  plants a defect in a scratch copy of each leg and requires the
#             gate above to FAIL on it: an Admitted proof, a sorry, a user
#             axiom, and a one-clause drift in a restated definition (caught
#             by the bridge theorems). A gate that has never been seen to
#             fail is not a gate.
#
# Fails closed: a missing or wrong-version prover is a FAIL, never a skip, and
# an axiom audit that inspects zero declarations is a FAIL, not a vacuous pass
# (the defect found in hyperpolymath/mathesis THY-1's Lean leg, 2026-11-16).
#
# Exit: 0 = pass; 1 = fail; 2 = misuse.

set -euo pipefail

MODE="${1:-}"
cd "$(dirname "${BASH_SOURCE[0]}")/.."
ROCQ_FILE="verification/proofs/rocq/RatifiedOrder.v"
LEAN_FILE="verification/proofs/lean4/ratified-order/RatifiedOrder.lean"
ROCQ_VERSION="${ROCQ_VERSION:-8.18.0}"
LEAN_VERSION="${LEAN_VERSION:-4.16.0}"

fail() { echo "FAIL: $*" >&2; exit 1; }

need_rocq() {
  command -v coqc >/dev/null 2>&1 || fail "coqc not on PATH (a missing prover fails this gate; it never skips)"
  coqc --version | grep -qF "version ${ROCQ_VERSION}" ||
    fail "coqc is not version ${ROCQ_VERSION}: $(coqc --version | head -1)"
}

need_lean() {
  command -v lean >/dev/null 2>&1 || fail "lean not on PATH (a missing prover fails this gate; it never skips)"
  lean --version | grep -qF "version ${LEAN_VERSION}" ||
    fail "lean is not version ${LEAN_VERSION}: $(lean --version | head -1)"
}

# rocq_audit FILE -> prints the receipt line; returns 1 on any defect.
rocq_audit() {
  local src="$1" dir base names expect got out rc
  dir="$(mktemp -d)"; base="AuditRatifiedOrder"
  names="$(sed -n -E "s/^[[:space:]]*(Theorem|Lemma)[[:space:]]+([A-Za-z_][A-Za-z0-9_']*).*/\2/p" "$src")"
  expect="$(grep -c . <<<"$names" || true)"
  if [ "$expect" -eq 0 ]; then echo "rocq audit: no Theorem or Lemma declared (empty domain)"; rm -rf "$dir"; return 1; fi
  { cat "$src"; echo; while IFS= read -r n; do echo "Print Assumptions $n."; done <<<"$names"; } >"$dir/$base.v"
  set +e; out="$(cd "$dir" && coqc "$base.v" 2>&1)"; rc=$?; set -e
  rm -rf "$dir"
  got="$(grep -c '^Closed under the global context' <<<"$out" || true)"
  if [ "$rc" -ne 0 ] || [ "$got" -ne "$expect" ]; then
    echo "rocq audit: $got of $expect declaration(s) closed under the global context (coqc exit $rc)"
    grep -v '^Closed under the global context' <<<"$out" | head -20
    return 1
  fi
  echo "Print Assumptions: closed under the global context for $expect of $expect declaration(s)"
}

# lean_check FILE -> prints the receipt line; returns 1 on any defect.
lean_check() {
  local src="$1" dir out rc declared audited
  set +e; out="$(lean "$src" 2>&1)"; rc=$?; set -e
  if [ "$rc" -ne 0 ] || grep -qE '(^|: )(error|warning)' <<<"$out"; then
    echo "lean: the file does not check cleanly (exit $rc)"; grep -E 'error|warning' <<<"$out" | head -20; return 1
  fi
  dir="$(mktemp -d)"
  { echo "import Lean"; cat "$src"; cat <<'LEAN'

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut n := 0
  for (name, ci) in env.constants.map₂.toList do
    -- Only what the source declares: theorems, and defs that carry a
    -- declaration range (the lemmas Lean generates have none).
    let isThm := match ci with | .thmInfo _ => true | _ => false
    let isDef := match ci with | .defnInfo _ => true | _ => false
    unless isThm || isDef do continue
    if (← liftCoreM (findDeclarationRanges? name)).isNone then continue
    if isThm then n := n + 1
    let axs ← liftCoreM (Lean.collectAxioms name)
    unless axs.isEmpty do
      logInfo m!"GATE-AXIOMS {name}: {axs.toList}"
  logInfo m!"GATE-AUDIT-DONE {n}"
LEAN
  } >"$dir/Audit.lean"
  set +e; out="$(lean "$dir/Audit.lean" 2>&1)"; rc=$?; set -e
  rm -rf "$dir"
  declared="$(grep -cE '^[[:space:]]*theorem[[:space:]]' "$src" || true)"
  audited="$(sed -n 's/.*GATE-AUDIT-DONE \([0-9]*\).*/\1/p' <<<"$out")"
  if [ "$rc" -ne 0 ] || [ -z "$audited" ] || grep -q 'GATE-AXIOMS' <<<"$out"; then
    echo "lean audit: a declaration depends on an axiom, or the audit did not run (exit $rc)"
    grep -E 'GATE-|error' <<<"$out" | head -20; return 1
  fi
  if [ "$audited" -eq 0 ] || [ "$audited" -ne "$declared" ]; then
    echo "lean audit: audited $audited theorem(s), the source declares $declared (an empty or partial domain fails)"; return 1
  fi
  echo "axioms: none for $audited of $declared declared theorem(s), and none for any def they use"
}

case "$MODE" in
  rocq)
    need_rocq
    echo "=== Rocq recheck leg: $ROCQ_FILE ($(coqc --version | head -1)) ==="
    dir="$(mktemp -d)"; cp "$ROCQ_FILE" "$dir/"
    ( cd "$dir" && coqc "$(basename "$ROCQ_FILE")" ) || { rm -rf "$dir"; fail "coqc rejects $ROCQ_FILE"; }
    rm -rf "$dir"
    rocq_audit "$ROCQ_FILE" || fail "Rocq axiom audit"
    echo "sha256 $(sha256sum "$ROCQ_FILE" | cut -d' ' -f1)  $ROCQ_FILE"
    echo "PASS: Rocq recheck leg"
    ;;
  lean)
    need_lean
    echo "=== Lean recheck leg: $LEAN_FILE ($(lean --version | head -1)) ==="
    lean_check "$LEAN_FILE" || fail "Lean check or axiom audit"
    echo "sha256 $(sha256sum "$LEAN_FILE" | cut -d' ' -f1)  $LEAN_FILE"
    echo "PASS: Lean recheck leg"
    ;;
  controls)
    need_rocq; need_lean
    t="$(mktemp -d)"; trap 'rm -rf "$t"' EXIT
    bad=0
    expect_fail() { # $1 label, $2 command...
      local label="$1"; shift
      if "$@" >"$t/log" 2>&1; then echo "CONTROL NOT CAUGHT: $label"; cat "$t/log"; bad=1
      else echo "caught: $label -- $(grep -m1 -E . "$t/log")"; fi
    }
    # Rocq: an Admitted proof compiles; the audit must still refuse it.
    sed '0,/^Proof\. intros \[\]; reflexivity\. Qed\./s//Proof. Admitted./' "$ROCQ_FILE" >"$t/A.v"
    grep -q 'Admitted\.' "$t/A.v" || fail "control setup: no Admitted planted"
    expect_fail "Rocq Admitted proof" rocq_audit "$t/A.v"
    # Rocq: a one-clause drift in a restated definition. withheld ▷b intact
    # = intact keeps every restated theorem TRUE (▷b stays monotone), so only
    # the bridge can see it; the failure must be at bridge_bcomp.
    sed 's/^  | withheld, intact   => withheld$/  | withheld, intact   => intact/' "$ROCQ_FILE" >"$t/D.v"
    cmp -s "$ROCQ_FILE" "$t/D.v" && fail "control setup: no Rocq drift planted"
    bl="$(grep -n '^Theorem bridge_bcomp' "$t/D.v" | cut -d: -f1)"
    el="$( (cd "$t" && coqc D.v 2>&1 || true) | sed -n 's/^File .*, line \([0-9]*\),.*/\1/p' | head -1)"
    if [ -n "$el" ] && [ "$el" -ge "$bl" ] && [ "$el" -le "$((bl + 1))" ]; then
      echo "caught: Rocq definition drift (bcomp), caught by the bridge -- first error at line $el (bridge_bcomp)"
    else echo "CONTROL NOT CAUGHT (or not by the bridge): Rocq definition drift, first error line '${el}'"; bad=1; fi
    # Lean: a sorry only warns; the gate must refuse it.
    { cat "$LEAN_FILE"; printf '\ntheorem planted_sorry : 1 = 2 := sorry\n'; } >"$t/S.lean"
    expect_fail "Lean sorry" lean_check "$t/S.lean"
    # Lean: a user axiom compiles without warning; the audit must refuse it.
    { cat "$LEAN_FILE"; printf '\naxiom planted_ax : False\ntheorem planted_use : 1 = 2 := planted_ax.elim\n'; } >"$t/X.lean"
    expect_fail "Lean user axiom" lean_check "$t/X.lean"
    # Lean: the same drift; the only error must be at bridge_bcomp.
    sed 's/^  | withheld, intact   => withheld$/  | withheld, intact   => intact/' "$LEAN_FILE" >"$t/D.lean"
    cmp -s "$LEAN_FILE" "$t/D.lean" && fail "control setup: no Lean drift planted"
    bl="$(grep -n '^theorem bridge_bcomp' "$t/D.lean" | cut -d: -f1)"
    errs="$(lean "$t/D.lean" 2>&1 | grep -E ': error' || true)"
    if [ -n "$errs" ] && ! grep -vq "D.lean:$bl:" <<<"$errs"; then
      echo "caught: Lean definition drift (bcomp), caught by the bridge -- only error at line $bl (bridge_bcomp)"
    else echo "CONTROL NOT CAUGHT (or not by the bridge): Lean definition drift"; echo "$errs"; bad=1; fi
    # Lean: an audit over an empty domain must fail, not pass vacuously.
    printf 'def onlyADef : Nat := 1\n' >"$t/E.lean"
    expect_fail "Lean empty audit domain" lean_check "$t/E.lean"
    [ "$bad" -eq 0 ] || fail "a planted defect was not caught"
    echo "PASS: every planted defect was caught (6 controls)"
    ;;
  *) echo "usage: $(basename "$0") rocq|lean|controls" >&2; exit 2 ;;
esac
