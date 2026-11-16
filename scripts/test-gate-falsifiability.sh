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
# A canary is only evidence if it actually plants the drift it names and the gate
# then objects to THAT drift. Three ways this harness used to pass without doing
# either, all measured 2026-11-09:
#   (a) the canary's own jq program fails -> jq writes an empty ledger -> the gate
#       rejects it for being invalid JSON -> the canary scores PASS having never
#       exercised its target. All six jq-driven canaries did this when corrupted.
#   (b) the jq program silently selects nothing (a renamed key, a .id that matches
#       no theorem) -> the ledger is unchanged -> an unchanged ledger is not a
#       wrong fixture, yet the gate's rejection of something else scored PASS.
#   (c) the gate rejects for an unrelated reason. "reject" alone is too weak, so a
#       reject canary now declares the reason it expects to see.
# $4 is that expected reason, an ERE matched against the gate's combined output.
pwg_case() {
  local want="$1" label="$2" jqprog="$3" whynot="${4:-}"
  local d got out
  d=$(scratch)
  mkdir -p "$d/scripts" "$d/verification" "$d/docs/status"
  cp "$ROOT/scripts/pwg-derive.sh" "$d/scripts/" 2>/dev/null || { rm -rf "$d"; bad "$label (no pwg-derive.sh to copy)"; return; }
  cp "$ROOT/scripts/pwg-check.sh"  "$d/scripts/" 2>/dev/null || { rm -rf "$d"; bad "$label (no pwg-check.sh to copy)"; return; }
  cp "$ROOT/docs/status/PROOF-STATUS.adoc" "$d/docs/status/" 2>/dev/null || { rm -rf "$d"; bad "$label (no PROOF-STATUS.adoc to copy — rule 5 would be untested)"; return; }
  # Rule 6 resolves witness names against the real sources: carry the inventory
  # script, the comment stripper it reads through, and the Agda/Lean sources.
  cp "$ROOT/scripts/pwg-names.sh" "$d/scripts/" 2>/dev/null || { rm -rf "$d"; bad "$label (no pwg-names.sh to copy — rule 6 would be untested)"; return; }
  mkdir -p "$d/tests/lib" "$d/verification/proofs/agda/theorem-b"
  if ! { cp "$ROOT/tests/lib/strip-proof-comments.awk" "$d/tests/lib/" \
         && cp -r "$ROOT/verification/proofs/agda/theorem-b/TB" "$d/verification/proofs/agda/theorem-b/" \
         && (cd "$ROOT/verification/proofs" && find lean4 -name '*.lean' -not -path '*/.lake/*' -print0 | xargs -0 cp --parents -t "$d/verification/proofs/"); }; then
    rm -rf "$d"; bad "$label (could not copy the sources rule 6 resolves against)"; return
  fi
  if [ "$jqprog" = "IDENTITY" ]; then
    cp "$ROOT/verification/pwg.json" "$d/verification/pwg.json"
  elif [ "$jqprog" = "PRETTY" ]; then
    # valid JSON, but not canonical JCS: pretty-printed with unsorted keys
    if ! jq . "$ROOT/verification/pwg.json" > "$d/verification/pwg.json" 2>"$d/jq.err"; then
      local why; why=$(head -1 "$d/jq.err" 2>/dev/null || true)
      rm -rf "$d"; bad "$label (the canary's OWN jq transform failed: $why)"; return
    fi
  else
    if ! jq -cS "$jqprog" "$ROOT/verification/pwg.json" > "$d/verification/pwg.json" 2>"$d/jq.err"; then
      local why; why=$(head -1 "$d/jq.err" 2>/dev/null || true)
      rm -rf "$d"; bad "$label (the canary's OWN jq transform failed: $why)"; return
    fi
    if jq -cS . "$ROOT/verification/pwg.json" | cmp -s - "$d/verification/pwg.json"; then
      rm -rf "$d"; bad "$label (the jq transform changed nothing — the fixture is not actually wrong)"; return
    fi
  fi
  if out=$(bash "$d/scripts/pwg-check.sh" "$d" 2>&1); then got=accept; else got=reject; fi
  rm -rf "$d"
  if [ "$got" != "$want" ]; then bad "$label (gate said $got, expected $want)"; return; fi
  if [ "$want" = reject ] && [ -n "$whynot" ] && ! printf '%s' "$out" | grep -qE "$whynot"; then
    bad "$label (rejected, but for the WRONG reason — wanted /$whynot/, got: $(printf '%s' "$out" | head -1))"; return
  fi
  ok "$label"
}

pwg_canaries() {
  [ -x "$PWG_GATE" ] || { bad "scripts/pwg-check.sh is missing — the PWG gate cannot be falsified"; return; }

  # Control first: a suite that always fires proves nothing.
  pwg_case accept "the real PWG ledger and status file are ACCEPTED" IDENTITY

  # 1. A grade asserted in the evidence file is drift by construction.
  pwg_case reject "a hand-asserted pwg on a theorem is rejected" \
    '.theorems[0].pwg = "1"' \
    "assert a grade"

  # 2. Canonical JCS is the estate's JSON serialisation (owner ruling D306).
  pwg_case reject "a non-canonical (pretty-printed) ledger is rejected" PRETTY

  # 3. Section 5's vocabulary is closed.
  pwg_case reject "a section 5 token outside the closed vocabulary is rejected" \
    '.theorems[0].legs.agda.token = "MOSTLY-PROVEN"' \
    "section 5 closed vocabulary"

  # 4. So is 2.2's.
  pwg_case reject "a 2.2 correspondence state outside the closed vocabulary is rejected" \
    '.theorems[0].legs.lean.state = "LOOKS-FINE"' \
    "correspondence state\\(s\\) outside the closed vocabulary"

  # 5. 8.2 requires the receipt to name the full 40-character commit.
  pwg_case reject "a receipt with a short commit is rejected" \
    '.receipts["agda-c0eb4f1"].commit = "c0eb4f1"' \
    "not a full 40-char sha"

  # 6. LOAD-BEARING: drop the import cone and the Agda leg no longer satisfies
  #    8.2's PWG-3 receipt requirement, so every derived grade that rested on it
  #    falls to ungraded and the published table stops matching. This fires only
  #    if the table really is derived.
  pwg_case reject "removing the import cone changes the derived grades and is rejected" \
    '.receipts["agda-c0eb4f1"].import_cone = ""' \
    "not the derived one"

  # 7. LOAD-BEARING the other way: flip a BRIDGE-PENDING Lean leg to RECONCILED
  #    and it starts to count, lifting that obligation to PWG-2i. The published
  #    table must stop matching.
  pwg_case reject "flipping a Lean leg to RECONCILED changes the grade and is rejected" \
    '(.theorems[] | select(.id == "L1") | .legs.lean.state) |= "RECONCILED"' \
    "not the derived one"
  # R11. A grade may not outlive the run that earned it. Measured against main
  # 0dceab6 these two PASSED the gate: the derivation read .state but never
  # .result, so a receipt recording the checker REJECTING the development still
  # carried 17 PWG-3 grades, and an unrecognised result was not a pass but was
  # not an error either. Both canaries FAIL against the pre-fix scripts.
  # "fail" is a LEGITIMATE recorded value, so rule 3 admits it; the rejection
  # must come from the grades themselves collapsing. Measured 2026-11-16: with
  # the Agda receipt at result=fail the census goes PWG-3 17 -> 0 and ungraded
  # 7 -> 24, so the published table is no longer the derived one. Against the
  # pre-fix scripts the census was byte-identical and this canary did not fire.
  pwg_case reject "a receipt that records result=fail cannot support a grade" \
    '.receipts["agda-c0eb4f1"].result = "fail"' \
    "not the derived one"
  pwg_case reject "a receipt result outside the closed vocabulary is rejected" \
    '.receipts["agda-c0eb4f1"].result = "probably-fine"' \
    "result must be pass|fail"
  # `$` in a regex can match before a final newline. Require the vocabulary
  # diagnostic so rejection for derived-table drift cannot mask this defect.
  pwg_case reject "a receipt result with a trailing newline is rejected" \
    '.receipts["agda-c0eb4f1"].result = "pass\n"' \
    "result must be pass[|]fail"
  # The same defect in the seven sibling anchors: jq's $ accepts a final
  # newline, so a 40-hex commit + "\n" and a token + "\n" were admitted. The
  # anchors are now \\A...\\z. Both canaries FAIL against the pre-fix scripts.
  pwg_case reject "a receipt commit with a trailing newline is rejected" \
    '.receipts["agda-c0eb4f1"].commit += "\n"' \
    "not a full 40-char sha"
  pwg_case reject "a section 5 token with a trailing newline is rejected" \
    '.theorems[0].legs.agda.token += "\n"' \
    "section 5 closed vocabulary"
  # R12. A witness must name something. Measured against main 0dceab6: 13 of 91
  # distinct witness names resolved to no declaration (L2's only Agda witness
  # among them) and the gate passed, because nothing read `declarations`. Both
  # canaries FAIL against the pre-rule-6 gate. The first plants the exact ASCII
  # transliteration that was live on main; the second a Lean name whose
  # namespace exists but holds no such declaration.
  pwg_case reject "an Agda witness spelled in ASCII (|> for ▷) does not resolve" \
    '(.theorems[] | select(.id == "L3") | .legs.agda.declarations) |= map(sub("▷"; "|>"))' \
    "resolve to no declaration"
  pwg_case reject "a Lean witness in the wrong namespace does not resolve" \
    '(.theorems[] | select(.id == "L1") | .legs.lean.declarations) = ["Trope.Bond.comp_assoc"]' \
    "resolve to no declaration"
  # A real name with a tab and text appended. The first rule-6 version split
  # the citation on the tab and resolved the real prefix, ignoring the rest;
  # this canary FAILS against it. Review on #119.
  pwg_case reject "a witness with a tab-joined suffix does not resolve" \
    '(.theorems[] | select(.id == "L1") | .legs.agda.declarations) |= map(. + "\tjunk")' \
    "resolve to no declaration"
}

# --- the top of the ladder: PWG-2ii and PWG-1 are different rungs ----------
# The table-drift gate cannot tell 1 from 2ii (either way the published row stops
# matching), so these canaries read the DERIVED grade directly. Both legs of L1
# are made to count; the only variable is the commit the receipts record.
# Measured 2026-11-16: against the pre-fix derivation a receipt commit of all
# f's derived PWG-1 -- "2ii" was unreachable, because the branch tested only
# conjuncts that counting had already implied. The 2ii canary FAILS against it.
derive_case() {
  local want="$1" label="$2" commit="$3" d got
  d=$(scratch)
  if ! jq -cS --arg c "$commit" '
      .receipts["rocq-canary"] = (.receipts["lean-boundary-c0eb4f1"] + {commit: $c})
      | .receipts["lean-boundary-c0eb4f1"].commit = $c
      | (.theorems[] | select(.id == "L1") | .legs) |=
          (.lean.state = "RECONCILED"
           | .rocq = {declarations: [], receipts: ["rocq-canary"], route: "re-proved", state: "RECONCILED", token: "PROVEN"})' \
      "$ROOT/verification/pwg.json" > "$d/pwg.json" 2>/dev/null; then
    rm -rf "$d"; bad "$label (the canary's OWN jq transform failed)"; return
  fi
  got=$(bash "$ROOT/scripts/pwg-derive.sh" --ledger "$d/pwg.json" --json 2>/dev/null | jq -r '.[] | select(.id == "L1") | .pwg')
  rm -rf "$d"
  if [ "$got" = "$want" ]; then ok "$label"; else bad "$label (derived PWG-$got, expected PWG-$want)"; fi
}
ladder_canaries() {
  local src
  src=$(jq -r '.commit' "$ROOT/verification/pwg.json")
  derive_case 1 "both legs counting, receipts on the source commit, derive PWG-1 (control)" "$src"
  derive_case 2ii "both legs counting, receipts on another commit, derive PWG-2ii, not PWG-1" \
    "$(printf '%040d' 0 | tr 0 f)"
}

# --- the comment stripper every dangerous-construct gate reads through ------
# Lean /- -/, Agda/Idris2 {- -} and Coq (* *) block comments NEST. Measured
# 2026-11-16 against the pre-fix stripper: a forbidden word inside a nested
# comment leaked into the scan (fail-loud), and an unterminated NESTED comment
# exited 0 -- a truncated scan reported as complete. Both canaries FAIL against
# the pre-fix stripper. The fixture words are assembled at runtime (see the
# header: a literal would trip the very scanners these canaries guard).
strip_canaries() {
  local d strip="$ROOT/tests/lib/strip-proof-comments.awk" w
  w="so""rry"
  d=$(scratch)
  printf '/- outer /- inner -/ %s stays inside -/\ntheorem t : True := trivial\n' "$w" > "$d/nested.lean"
  if awk -f "$strip" "$d/nested.lean" 2>/dev/null | grep -qw "$w"; then
    bad "a word inside a NESTED Lean comment leaks into the scan"
  else
    ok "a word inside a NESTED Lean comment is stripped"
  fi
  printf '{- a {- b -} c\nx : Set\n' > "$d/open.agda"
  if awk -f "$strip" "$d/open.agda" >/dev/null 2>&1; then
    bad "an unterminated NESTED Agda comment was reported as a complete scan"
  else
    ok "an unterminated NESTED Agda comment fails the stripper loudly"
  fi
  rm -rf "$d"
}

# --- META (R10 applied to R10): the suite must detect breakage in ITS OWN fixtures.
# A canary whose jq program is broken writes an empty ledger; the gate then rejects
# it for being invalid JSON rather than for the planted drift, and the canary passes
# without ever exercising its target. This plants exactly that and asserts the suite
# reports FAILURE. Measured: this canary FAILS against the pre-fix harness.
meta_canary() {
  local out
  # Isolation by subshell is the POINT: the meta-probe is MEANT to fail, and its
  # failure must not reach the suite tally. Read its VERDICT LINE rather than a
  # counter. An earlier version shadowed PASS/FAIL inside the substitution to
  # discard them; that worked, but ShellCheck then marked every later read of
  # those names SC2031 across the whole tally block, and silencing ten warnings
  # on the real counters to keep one deliberate shadow is a bad trade -- it
  # blinds the check where it would do genuine work. Nothing is assigned here
  # that the outer shell reads, so the warnings go away by construction instead
  # of by suppression.
  out=$( pwg_case reject "meta-probe (expected to be reported as FAILING)" '.theorems[0].pwg = ' 2>&1 )
  if printf '%s\n' "$out" | grep -q '^FAIL '; then
    ok "a canary whose own jq program is broken is reported as FAILURE (meta-canary)"
  else
    bad "a BROKEN canary still reported PASS — the suite cannot detect its own breakage"
  fi
}

wellknown_canaries; valid_canary; live_canary
c_weak_crypto; c_plaintext_http; c_secret
pwg_canaries; ladder_canaries; strip_canaries
meta_canary
echo
# A canary group that silently stops running used to report "10/10" and exit 0.
# The count is part of the claim.
EXPECTED_CASES=31
if [ "$((PASS+FAIL))" -ne "$EXPECTED_CASES" ]; then
  echo "gate falsifiability canaries: $((PASS+FAIL)) cases ran, $EXPECTED_CASES expected — a canary group did not run"
  exit 1
fi
if [ "$FAIL" -gt 0 ]; then
  echo "gate falsifiability canaries: $PASS/$((PASS+FAIL)) — FAILED"
  echo "A gate whose canary does not fire cannot fail, and is not a gate."
  exit 1
fi
echo "gate falsifiability canaries: $PASS/$PASS"
