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
  printf 'fn h() { md5(x) }\n' > "$d/lib.rs"
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
  printf 'const u = "http://data.internal.invalid/x";\n' > "$d/app.rs"
  local hit
  hit=$(cd "$d" && grep -rE 'http://[^l][^o][^c]' --include="*.rs" . 2>/dev/null \
        | grep -v 'localhost\|127.0.0.1\|example\|test\|spec' | head -5 || true)
  rm -rf "$d"
  if [ -n "$hit" ]; then ok "plaintext HTTP is detected"
  else bad "plaintext HTTP NOT detected — the security gate is blind to it"; fi
}

c_secret() {
  local d; d=$(scratch)
  printf 'let api_key = "AAAABBBBCCCCDDDDEEEEFFFFGGGG1234";\n' > "$d/cfg.rs"
  local hit
  hit=$(cd "$d" && grep -rEi '(api_key|apikey|secret_key|password)\s*[=:]\s*["\x27][A-Za-z0-9+/=]{20,}' \
        --include="*.rs" . 2>/dev/null | grep -v 'example\|sample\|test\|mock\|placeholder' | head -3 || true)
  rm -rf "$d"
  if [ -n "$hit" ]; then ok "hardcoded secret is detected"
  else bad "hardcoded secret NOT detected — the security gate is blind to it"; fi
}

wellknown_canaries; valid_canary; live_canary
c_weak_crypto; c_plaintext_http; c_secret
echo
if [ "$FAIL" -gt 0 ]; then
  echo "gate falsifiability canaries: $PASS/$((PASS+FAIL)) — FAILED"
  echo "A gate whose canary does not fire cannot fail, and is not a gate."
  exit 1
fi
echo "gate falsifiability canaries: $PASS/$PASS"
