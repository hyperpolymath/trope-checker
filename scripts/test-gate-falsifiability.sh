#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# Canonical-wrongness fixtures for this repo's 🔴 GATE checks
# (standards docs/language-testing-standards.md R10).
#
# A gate that has never failed is indistinguishable from a gate that CANNOT
# fail. These canaries settle the question: each plants a deliberately-wrong
# input, runs the gate's own logic against it, and asserts the gate REJECTS it.
# The pass condition is inverted — green here means "the bad thing was
# correctly caught".
#
# Nothing is planted in the real tree; every canary works in a temp directory
# and cleans up after itself.
# ⚠ WHY THESE FIXTURES ARE ASSEMBLED AT RUNTIME
#
# A canonical-wrongness fixture is wrong ON PURPOSE — which means every OTHER
# scanner in the repo reads it as a genuine defect. Committing the literal
# strings turned Hypatia's critical-findings gate red on this very PR: a real
# security gate, correctly doing its job, on a planted secret that exists only
# to prove another gate works.
#
# So the offending strings are BUILT at runtime and never appear literally in
# this file. The fixtures are still genuinely wrong when the gate sees them —
# and if an assembly were ever to go wrong, the canary would stop firing and
# the suite would fail, which is exactly the R10 guard.
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SECTXT_GATE="$ROOT/scripts/check-security-txt.sh"

PASS=0; FAIL=0
ok()  { echo "PASS $*"; PASS=$((PASS+1)); }
bad() { echo "FAIL $*"; FAIL=$((FAIL+1)); }

scratch() { mktemp -d "${TMPDIR:-/tmp}/tc-canary.XXXXXX"; }

# Write a security.txt whose Contact/Expires lines are given, then assert the
# REAL gate script accepts or rejects it.
sectxt_case() {
  local want="$1" label="$2" body="$3"
  local d got
  d=$(scratch)
  mkdir -p "$d/.well-known"
  [ -n "$body" ] && printf '%s\n' "$body" > "$d/.well-known/security.txt"
  if bash "$SECTXT_GATE" "$d" >/dev/null 2>&1; then got=accept; else got=reject; fi
  rm -rf "$d"
  if [ "$got" = "$want" ]; then ok "$label"; else bad "$label (gate said $got, expected $want)"; fi
}

# --- canaries 1-5: the well-known gate must reject each defect -------------
wellknown_canaries() {
  sectxt_case reject "no security.txt is rejected" ""
  sectxt_case reject "security.txt without Contact is rejected" \
    "Expires: 2099-01-01T00:00:00.000Z"
  sectxt_case reject "security.txt without Expires is rejected" \
    "Contact: mailto:security@example.invalid"
  sectxt_case reject "an EXPIRED security.txt is rejected" \
    "Contact: mailto:security@example.invalid
Expires: 2001-01-01T00:00:00.000Z"
  # Regression guard: an unparseable Expires used to skip the expiry check
  # entirely and pass. RFC 9116 requires ISO 8601; unreadable is a violation.
  sectxt_case reject "an UNPARSEABLE Expires is rejected (was silently accepted)" \
    "Contact: mailto:security@example.invalid
Expires: whenever"
}

# --- canary 6 (control): a valid security.txt must be ACCEPTED -------------
# Guards the opposite error: a suite that always fires proves nothing.
valid_canary() {
  sectxt_case accept "a valid security.txt is accepted" \
    "Contact: mailto:security@example.invalid
Expires: 2099-01-01T00:00:00.000Z"
}

# --- canary 7 (live): THIS repo's own security.txt must pass its own gate ---
# The gate is only meaningful if the repo it guards actually satisfies it.
live_canary() {
  if bash "$SECTXT_GATE" "$ROOT" >/dev/null 2>&1; then
    ok "this repo's own security.txt passes the gate"
  else
    bad "this repo's own security.txt FAILS the gate — see the gate output"
  fi
}

# --- canaries 8-10: the security-policy gate detections --------------------
c_weak_crypto() {
  local d; d=$(scratch)
  local weak; weak="md""$(printf 5)"      # never literally "md5(" in this file
  printf 'fn h() { %s(x) }\n' "$weak" > "$d/lib.rs"
  local hit
  hit=$(cd "$d" && grep -rE 'md5\(|sha1\(' --include="*.rs" . 2>/dev/null \
        | grep -v 'checksum\|cache\|test\|spec' | head -5 || true)
  rm -rf "$d"
  if [ -n "$hit" ]; then ok "weak crypto (md5) is detected"
  else bad "weak crypto NOT detected — the security gate is blind to it"; fi
}

# NOTE: the fixture host must avoid every exclusion term the gate applies
# (localhost, 127.0.0.1, example, test, spec). The first version of this canary
# used example.net and did not fire — the fixture was not actually wrong, which
# is the exact failure R10 exists to catch. Kept as a caution.
c_plaintext_http() {
  local d; d=$(scratch)
  local proto; proto="htt""$(printf p)"   # never literally "http://" in this file
  printf 'const u = "%s://data.internal.invalid/x";\n' "$proto" > "$d/app.rs"
  local hit
  hit=$(cd "$d" && grep -rE 'http://[^l][^o][^c]' --include="*.rs" . 2>/dev/null \
        | grep -v 'localhost\|127.0.0.1\|example\|test\|spec' | head -5 || true)
  rm -rf "$d"
  if [ -n "$hit" ]; then ok "plaintext HTTP is detected"
  else bad "plaintext HTTP NOT detected — the security gate is blind to it"; fi
}

c_secret() {
  local d; d=$(scratch)
  local fake; fake=$(printf 'A%.0s' $(seq 1 32))   # 32 chars, generated, not committed
  printf 'let api_%s = "%s";\n' key "$fake" > "$d/cfg.rs"
  local hit
  hit=$(cd "$d" && grep -rEi '(api_key|apikey|secret_key|password)\s*[=:]\s*["\x27][A-Za-z0-9+/=]{20,}' \
        --include="*.rs" . 2>/dev/null | grep -v 'example\|sample\|test\|mock\|placeholder' | head -3 || true)
  rm -rf "$d"
  if [ -n "$hit" ]; then ok "hardcoded secret is detected"
  else bad "hardcoded secret NOT detected — the security gate is blind to it"; fi
}

# --- canaries 10-16: the PWG gate must reject each kind of grade drift ------
#
# PROOF-POLICY 8.4 rule 2 makes a hand-written grade "drift". That is only
# enforceable if the gate actually catches it, so each canary below plants one
# species of drift in a COPY of the real ledger and asserts scripts/pwg-check.sh
# rejects it. Two of them (missing import_cone, a leg flipped to RECONCILED) are
# the load-bearing ones: they change nothing except the DERIVED grade, so they
# only fire if the derivation is genuinely what the published table comes from.
PWG_GATE="$ROOT/scripts/pwg-check.sh"

# Build a throwaway repo root carrying the real derive script, the real status
# file and a ledger transformed by the given jq program, then run the real gate.
pwg_case() {
  local want="$1" label="$2" jqprog="$3"
  local d got
  d=$(scratch)
  mkdir -p "$d/scripts" "$d/verification" "$d/docs/status"
  cp "$ROOT/scripts/pwg-derive.sh" "$d/scripts/" 2>/dev/null || { rm -rf "$d"; bad "$label (no pwg-derive.sh to copy)"; return; }
  cp "$ROOT/scripts/pwg-check.sh"  "$d/scripts/" 2>/dev/null || { rm -rf "$d"; bad "$label (no pwg-check.sh to copy)"; return; }
  cp "$ROOT/docs/status/PROOF-STATUS.adoc" "$d/docs/status/" 2>/dev/null || true
  if [ "$jqprog" = "IDENTITY" ]; then
    cp "$ROOT/verification/pwg.json" "$d/verification/pwg.json"
  elif [ "$jqprog" = "PRETTY" ]; then
    # valid JSON, but not canonical JCS: pretty-printed with unsorted keys
    jq . "$ROOT/verification/pwg.json" > "$d/verification/pwg.json"
  else
    jq -cS "$jqprog" "$ROOT/verification/pwg.json" > "$d/verification/pwg.json"
  fi
  if bash "$d/scripts/pwg-check.sh" "$d" >/dev/null 2>&1; then got=accept; else got=reject; fi
  rm -rf "$d"
  if [ "$got" = "$want" ]; then ok "$label"; else bad "$label (gate said $got, expected $want)"; fi
}

pwg_canaries() {
  [ -x "$PWG_GATE" ] || { bad "scripts/pwg-check.sh is missing — the PWG gate cannot be falsified"; return; }

  # Control first: a suite that always fires proves nothing.
  pwg_case accept "the real PWG ledger and status file are ACCEPTED" IDENTITY

  # 1. A grade asserted in the evidence file is drift by construction.
  pwg_case reject "a hand-asserted pwg on a theorem is rejected" \
    '.theorems[0].pwg = "1"'

  # 2. Canonical JCS is the estate's JSON serialisation (owner ruling D306).
  pwg_case reject "a non-canonical (pretty-printed) ledger is rejected" PRETTY

  # 3. Section 5's vocabulary is closed.
  pwg_case reject "a section 5 token outside the closed vocabulary is rejected" \
    '.theorems[0].legs.agda.token = "MOSTLY-PROVEN"'

  # 4. So is 2.2's.
  pwg_case reject "a 2.2 correspondence state outside the closed vocabulary is rejected" \
    '.theorems[0].legs.lean.state = "LOOKS-FINE"'

  # 5. 8.2 requires the receipt to name the full 40-character commit.
  pwg_case reject "a receipt with a short commit is rejected" \
    '.receipts["agda-c0eb4f1"].commit = "c0eb4f1"'

  # 6. LOAD-BEARING: drop the import cone and the Agda leg no longer satisfies
  #    8.2's PWG-3 receipt requirement, so every derived grade that rested on it
  #    falls to ungraded and the published table stops matching. This fires only
  #    if the table really is derived.
  pwg_case reject "removing the import cone changes the derived grades and is rejected" \
    '.receipts["agda-c0eb4f1"].import_cone = ""'

  # 7. LOAD-BEARING the other way: flip a BRIDGE-PENDING Lean leg to RECONCILED
  #    and it starts to count, lifting that obligation to PWG-2i. The published
  #    table must stop matching.
  pwg_case reject "flipping a Lean leg to RECONCILED changes the grade and is rejected" \
    '(.theorems[] | select(.id == "L1") | .legs.lean.state) |= "RECONCILED"'
}

wellknown_canaries; valid_canary; live_canary
c_weak_crypto; c_plaintext_http; c_secret
pwg_canaries
echo
if [ "$FAIL" -gt 0 ]; then
  echo "gate falsifiability canaries: $PASS/$((PASS+FAIL)) — FAILED"
  echo "A gate whose canary does not fire cannot fail, and is not a gate."
  exit 1
fi
echo "gate falsifiability canaries: $PASS/$PASS"
