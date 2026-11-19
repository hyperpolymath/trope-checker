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
# A refusal counts only if why3find actually ran and its output names the intended
# control or mutated function. A setup error (missing why3find.json, no files,
# launch failure) is a gate failure, never a refusal.
# Regeneration is forced every time: sources are touched so Creusot's Cargo cache
# (target/creusot) cannot skip creusot-rustc, and verif/ is wiped.
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

# fresh_coma WS LOGFILE [CARGO ARGS...]: force regeneration, translate, require output.
fresh_coma() {
  local ws="$1" out="$2"; shift 2
  rm -rf "$ws/verif"
  find "$ws" "$root/src/rust/src" -name '*.rs' -not -path '*/target/*' -exec touch {} +
  if ! (cd "$ws" && cargo creusot --only=coma "$@") >"$out" 2>&1; then
    return 1
  fi
  [[ -n "$(find "$ws/verif" -name '*.coma' -print -quit 2>/dev/null)" ]]
}

# ── 1. the positive proof, on SCOPE only ──
echo "== prove: SCOPE of the verification crate (src/rust/src/lib.rs + creusot_spec.rs)"
if ! fresh_coma "$here" "$log/coma.log"; then
  echo "FAIL: translation to Coma failed or wrote no Coma file (see $log/coma.log)"
  tail -40 "$log/coma.log"
  exit 1
fi
for p in "${scope[@]}"; do
  if ! (cd "$here" && cargo creusot --only=prove --dry-run-why3find "$p") >"$log/scope-check.log" 2>&1; then
    echo "FAIL: SCOPE pattern '$p' matches no Coma file"
    fail=1
  fi
done
(cd "$here" && find verif -name '*.coma' | sort) >"$log/all-coma.txt"
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
  elif setup_error "$log/control-$c.log" || ! grep -q "$fn" "$log/control-$c.log"; then
    echo "FAIL: control $c failed without a prover verdict naming $fn (see $log/control-$c.log)"
    fail=1
  else
    echo "refused (good): control $c"
  fi
done

# ── 3. the mutants ──
while IFS=$'\t' read -r id fn old new; do
  [[ -z "${id}" || "${id}" == \#* ]] && continue
  work="$(mktemp -d)"
  mkdir -p "$work/src/rust" "$work/verification"
  cp -r "$root/src/rust/src" "$work/src/rust/src"
  cp "$root/src/rust/Cargo.toml" "$work/src/rust/"
  cp -r "$here" "$work/verification/creusot"
  rm -rf "$work/verification/creusot/target" "$work/verification/creusot/verif" \
         "$work/verification/creusot/controls/target" "$work/verification/creusot/controls/verif"
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
     || [[ -z "$(find "$work/verification/creusot/verif" -name '*.coma' -print -quit 2>/dev/null)" ]]; then
    echo "FAIL: mutant $id did not translate to Coma; a refusal would prove nothing"
    fail=1; rm -rf "$work"; continue
  fi
  if (cd "$work/verification/creusot" && cargo creusot --only=prove "${scope[@]}") >"$log/mutant-$id.log" 2>&1; then
    echo "FAIL: mutant $id ($fn) was PROVED. The contracts do not pin the code."
    fail=1
  elif setup_error "$log/mutant-$id.log" || ! grep -q "$fn" "$log/mutant-$id.log"; then
    echo "FAIL: mutant $id failed without a prover verdict naming $fn (see $log/mutant-$id.log)"
    fail=1
  else
    echo "refused (good): mutant $id ($fn)"
  fi
  rm -rf "$work"
done < "$here/mutants/MUTANTS"

if [[ "$fail" -ne 0 ]]; then
  echo "CREUSOT GATE: RED"
  exit 1
fi
echo "CREUSOT GATE: GREEN (SCOPE proved; ${#controls[@]} controls and every mutant refused)"
