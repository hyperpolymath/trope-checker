#!/usr/bin/env bash
# SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
# SPDX-License-Identifier: MPL-2.0
#
# Creusot gate for the Rust fast core. Fails loudly:
#   1. `cargo creusot` must be installed. A missing tool is exit 3 (OPEN), never 0.
#   2. The positive proof covers exactly the Coma files named in SCOPE. Every SCOPE
#      pattern must match at least one file. Files outside SCOPE are listed as OPEN.
#   3. Every planted control (controls/, one Cargo feature each) must translate to
#      Coma, produce its own Coma file, and then be REFUSED by the provers.
#   4. Every mutant (mutants/MUTANTS) must compile with plain rustc, translate to
#      Coma, and then be REFUSED by the provers on the SCOPE files.
# A refusal counts only on a positive why3find verdict on the intended function:
# "proof failed", "Goal Coma.vc_<fn>: ✘", "Error: <n> unproved file", and no
# other failing goal (see prover_refused). Any other failure fails the gate. A setup error (missing why3find.json, no files,
# launch failure) is a gate failure, never a refusal.
# Regeneration is forced every time: sources are touched so Creusot's Cargo cache
# (target/creusot) cannot skip creusot-rustc, and verif/ is wiped. A self-check
# reruns the crate and one control with identical inputs and a warm cache and
# requires every Coma file to be rewritten.
# Exit codes: 0 all good; 1 red; 3 Creusot not installed (OPEN).
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(cd "$here/../.." && pwd)"
# shellcheck source=/dev/null
source "$here/PINS"

if ! command -v cargo-creusot >/dev/null 2>&1; then
  echo "OPEN: cargo-creusot is not installed (pinned $CREUSOT_TAG @ $CREUSOT_SHA)." >&2
  echo "OPEN: nothing about the Rust core is proved by this run." >&2
  exit 3
fi
for ws in "$here" "$here/controls"; do
  [[ -f "$ws/why3find.json" ]] || { echo "FAIL: $ws/why3find.json missing"; exit 1; }
done

fail=0
COMA_GLOB="*.coma"
log="${CREUSOT_LOG_DIR:-$(mktemp -d)}"
mkdir -p "$log"
echo "logs: $log"
mapfile -t scope < <(grep -v '^#' "$here/SCOPE" | sed '/^[[:space:]]*$/d')
[[ "${#scope[@]}" -gt 0 ]] || { echo "FAIL: SCOPE is empty"; exit 1; }

# setup_error LOGFILE: true if the prove step failed before or outside the provers.
setup_error() {
  local logfile="$1"
  grep -qE "No files to prove|failed to launch|not found\. Perhaps|Pattern must be non-empty|could not compile" "$logfile"
}

# prover_refused LOGFILE FN: true only for a positive why3find verdict on FN.
# Format taken from real CI logs (run 44507269211, why3find 89dd8721): for each
# goal it cannot prove, why3find prints "<position>: proof failed" (the position
# is the Rust source span, or the .coma file for a logic lemma), then
# "Goal Coma.vc_<fn>: ✘ ...", and finally "Error: <n> unproved file". A refusal
# needs all three, a failing Goal line naming exactly vc_<fn>, and no failing
# Goal line for any other function. Anything else is an unrecognised failure.
# Note: why3find's ✘ means "not proved within the prover budget"; it does not
# distinguish a refutation from a timeout. See README "What a refusal means".
prover_refused() {
  local logfile="$1" fn="$2" plain others
  plain="$(sed 's/\x1b\[[0-9;]*m//g' "$logfile")"
  grep -q ': proof failed$' <<<"$plain" || return 1
  grep -qE '^Error: [0-9]+ unproved file' <<<"$plain" || return 1
  grep -qE "^ *Goal Coma\.vc_${fn}: ✘" <<<"$plain" || return 1
  others="$(grep -E '^ *Goal [^ ]+: ✘' <<<"$plain" | grep -vE "^ *Goal Coma\.vc_${fn}: ✘" || true)"
  [[ -z "$others" ]]
}

# show_log LOGFILE: print the prover output of an unrecognised failure into the CI
# log (colour codes stripped, build noise dropped), so the verdict can be read.
show_log() {
  local logfile="$1"
  sed 's/\x1b\[[0-9;]*m//g' "$logfile" \
    | grep -v -E '^ *(Compiling|Checking|Downloaded|Downloading|Updating|Locking|Finished) ' \
    | tail -60 | sed 's/^/    | /'
}

# coma_newer_than WS MARKER: Coma output exists, and every file is newer than MARKER.
coma_newer_than() {
  local ws="$1" marker="$2"
  [[ -n "$(find "$ws/verif" -name "$COMA_GLOB" -print -quit 2>/dev/null)" ]] \
    && [[ -z "$(find "$ws/verif" -name "$COMA_GLOB" ! -newer "$marker" -print -quit)" ]]
}

# fresh_coma WS LOGFILE [CARGO ARGS...]: force regeneration, translate, require output.
fresh_coma() {
  local ws="$1" out="$2"; shift 2
  rm -rf "$ws/verif"
  find "$ws" "$root/src/rust/src" -name '*.rs' -not -path '*/target/*' -exec touch {} +
  if ! (cd "$ws" && cargo creusot --only=coma "$@") >"$out" 2>&1; then
    return 1
  fi
  [[ -n "$(find "$ws/verif" -name "$COMA_GLOB" -print -quit 2>/dev/null)" ]]
}

# ── 1. the positive proof, on SCOPE only ──
echo "== prove: SCOPE of the verification crate (src/rust/src/lib.rs + creusot_spec.rs)"
if ! fresh_coma "$here" "$log/coma.log"; then
  echo "FAIL: translation to Coma failed or wrote no Coma file (see $log/coma.log)"
  # Every error with its context, not just the tail: a truncated log hid the
  # first error of an earlier run.
  grep -v -E '^ *(Compiling|Checking|Downloaded|Downloading|Updating|Locking) ' "$log/coma.log" | head -400
  exit 1
fi
# Regeneration self-check: translate again with the same inputs and a warm
# target/creusot. Every Coma file must be rewritten (newer than the marker), and
# the output must not be empty. A cache that skips creusot-rustc fails here.
marker="$(mktemp)"; sleep 1
if ! fresh_coma "$here" "$log/coma-rerun.log" || ! coma_newer_than "$here" "$marker"; then
  echo "FAIL: warm-cache rerun did not regenerate every Coma file (see $log/coma-rerun.log)"
  fail=1
else
  echo "regenerated (good): verification crate, warm cache, same inputs"
fi
for p in "${scope[@]}"; do
  if ! (cd "$here" && cargo creusot --only=prove --dry-run-why3find "$p") >"$log/scope-check.log" 2>&1; then
    echo "FAIL: SCOPE pattern '$p' matches no Coma file"
    fail=1
  fi
done
(cd "$here" && find verif -name "$COMA_GLOB" | sort) >"$log/all-coma.txt"
(cd "$here" && cargo creusot --only=prove --dry-run-why3find "${scope[@]}") 2>&1 \
  | tr -s ' "' '\n' | grep '\.coma$' | sort -u >"$log/in-scope.txt" || true
echo "Coma files: $(wc -l <"$log/all-coma.txt") total, $(wc -l <"$log/in-scope.txt") in SCOPE."
echo "OPEN (translated, not in SCOPE, not proved):"
comm -23 "$log/all-coma.txt" "$log/in-scope.txt" | sed 's/^/  /'
if (cd "$here" && cargo creusot --only=prove "${scope[@]}") >"$log/prove.log" 2>&1; then
  echo "PROVED: every SCOPE file"
else
  echo "FAIL: proofs did not go through (see $log/prove.log)"
  tail -60 "$log/prove.log"
  fail=1
fi

# ── 2. the planted controls ──
mapfile -t controls < <(sed -n 's/^\(c[0-9][0-9]_[a-z0-9_]*\) = \[\]$/\1/p' "$here/controls/Cargo.toml")
[[ "${#controls[@]}" -gt 0 ]] || { echo "FAIL: no controls found"; exit 1; }
for c in "${controls[@]}"; do
  fn="${c%%_*}"   # c03_meet_... -> c03, the control's function name
  if ! fresh_coma "$here/controls" "$log/control-$c-coma.log" -- --features "$c"; then
    echo "FAIL: control $c did not translate to Coma; a refusal would prove nothing"
    fail=1; continue
  fi
  if [[ -z "$(find "$here/controls/verif" -name "$fn*.coma" -print -quit)" ]]; then
    echo "FAIL: control $c produced no Coma file for $fn"
    fail=1; continue
  fi
  if (cd "$here/controls" && cargo creusot --only=prove "tropecheck_creusot_controls_rlib::$fn") >"$log/control-$c.log" 2>&1; then
    echo "FAIL: control $c was PROVED. A false contract went through."
    fail=1
  elif setup_error "$log/control-$c.log" || ! prover_refused "$log/control-$c.log" "$fn"; then
    echo "FAIL: control $c: unrecognised failure, no why3find 'proof failed' verdict on $fn (see $log/control-$c.log)"
    show_log "$log/control-$c.log"
    fail=1
  else
    echo "refused (good): control $c"
    sed 's/\x1b\[[0-9;]*m//g' "$log/control-$c.log" | grep -E ': proof failed|^ *Goal ' | head -6 | sed 's/^/    | /'
  fi
done

# Same self-check for a control: rerun the last control with the same feature.
c="${controls[-1]}"; fn="${c%%_*}"
marker="$(mktemp)"; sleep 1
if fresh_coma "$here/controls" "$log/control-$c-rerun.log" -- --features "$c" \
   && coma_newer_than "$here/controls" "$marker" \
   && [[ -n "$(find "$here/controls/verif" -name "$fn.coma" -newer "$marker" -print -quit)" ]]; then
  echo "regenerated (good): control $c, warm cache, same feature"
else
  echo "FAIL: control $c rerun did not regenerate its Coma (see $log/control-$c-rerun.log)"
  fail=1
fi

# ── 3. the mutants ──
while IFS=$'\t' read -r id fn old new; do
  [[ -z "${id}" || "${id}" == \#* ]] && continue
  work="$(mktemp -d)"
  mkdir -p "$work/src/rust" "$work/verification"
  cp -r "$root/src/rust/src" "$work/src/rust/src"
  cp "$root/src/rust/Cargo.toml" "$work/src/rust/"
  # Copy the verification tree without build output, so each mutant starts with
  # a fresh target/ and verif/ (both trees).
  (cd "$here" && find . \( -path ./target -o -path ./verif -o -path ./controls/target -o -path ./controls/verif \) -prune -o -type f -print0 \
     | while IFS= read -r -d '' f; do mkdir -p "$work/verification/creusot/$(dirname "$f")"; cp "$f" "$work/verification/creusot/$f"; done)
  n="$(grep -cF -- "$old" "$work/src/rust/src/lib.rs" || true)"
  if [[ "$n" != "1" ]]; then
    echo "FAIL: mutant $id ($fn): original text found $n times, expected 1"
    fail=1; rm -rf "$work"; continue
  fi
  # Literal (not glob) single replacement in pure bash.
  src="$(<"$work/src/rust/src/lib.rs")"
  printf '%s\n' "${src/"$old"/"$new"}" >"$work/src/rust/src/lib.rs"
  if ! (cd "$work/src/rust" && cargo check --offline -q) >"$log/mutant-$id-rustc.log" 2>&1; then
    echo "FAIL: mutant $id does not compile with plain rustc; it would be refused for the wrong reason"
    fail=1; rm -rf "$work"; continue
  fi
  if ! (cd "$work/verification/creusot" && cargo creusot --only=coma) >"$log/mutant-$id-coma.log" 2>&1 \
     || [[ -z "$(find "$work/verification/creusot/verif" -name "$COMA_GLOB" -print -quit 2>/dev/null)" ]]; then
    echo "FAIL: mutant $id did not translate to Coma; a refusal would prove nothing"
    fail=1; rm -rf "$work"; continue
  fi
  if (cd "$work/verification/creusot" && cargo creusot --only=prove "${scope[@]}") >"$log/mutant-$id.log" 2>&1; then
    echo "FAIL: mutant $id ($fn) was PROVED. The contracts do not pin the code."
    fail=1
  elif setup_error "$log/mutant-$id.log" || ! prover_refused "$log/mutant-$id.log" "$fn"; then
    echo "FAIL: mutant $id: unrecognised failure, no why3find 'proof failed' verdict on $fn (see $log/mutant-$id.log)"
    show_log "$log/mutant-$id.log"
    fail=1
  else
    echo "refused (good): mutant $id ($fn)"
    sed 's/\x1b\[[0-9;]*m//g' "$log/mutant-$id.log" | grep -E ': proof failed|^ *Goal ' | head -6 | sed 's/^/    | /'
  fi
  rm -rf "$work"
done < "$here/mutants/MUTANTS"

if [[ "$fail" -ne 0 ]]; then
  echo "CREUSOT GATE: RED"
  exit 1
fi
echo "CREUSOT GATE: GREEN (SCOPE proved; ${#controls[@]} controls and every mutant refused)"
