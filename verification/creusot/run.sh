#!/usr/bin/env bash
# SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
# SPDX-License-Identifier: MPL-2.0
#
# Creusot gate for the Rust fast core. Fails loudly:
#   1. `cargo creusot` must not be missing. A missing tool is exit 3 (OPEN), never 0.
#   2. The verification crate (whose root is src/rust/src/lib.rs) must prove.
#   3. Every planted control in controls/ must translate to Coma and then be
#      REFUSED by the provers, one feature at a time.
#   4. Every mutant in mutants/MUTANTS must still compile with plain rustc, translate
#      to Coma, AND be REFUSED by the provers. A mutant that does not compile proves nothing, so it
#      is a gate failure too.
# Exit codes: 0 all good; 1 a proof failed or a control/mutant was accepted;
# 3 Creusot not installed (OPEN).
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

fail=0
log="${CREUSOT_LOG_DIR:-$(mktemp -d)}"
mkdir -p "$log"
echo "logs: $log"

# ── 1. the proofs ──
echo "== prove: verification crate (src/rust/src/lib.rs + creusot_spec.rs)"
rm -rf "$here/verif"
if (cd "$here" && cargo creusot) >"$log/prove.log" 2>&1; then
  echo "PROVED"
else
  echo "FAIL: proofs did not go through (see $log/prove.log)"
  tail -40 "$log/prove.log"
  fail=1
fi

# ── 2. the planted controls ──
mapfile -t controls < <(sed -n 's/^\(c[0-9][0-9]_[a-z0-9_]*\) = \[\]$/\1/p' "$here/controls/Cargo.toml")
[[ "${#controls[@]}" -gt 0 ]] || { echo "FAIL: no controls found"; exit 1; }
for c in "${controls[@]}"; do
  # A control must COMPILE to Coma (else it is refused for the wrong reason),
  # then FAIL to prove. verif/ is wiped so no stale goal from another control counts.
  rm -rf "$here/controls/verif"
  if ! (cd "$here/controls" && cargo creusot --only=coma -- --features "$c") >"$log/control-$c-coma.log" 2>&1; then
    echo "FAIL: control $c did not translate to Coma; a refusal would prove nothing"
    fail=1; continue
  fi
  if (cd "$here/controls" && cargo creusot --only=prove) >"$log/control-$c.log" 2>&1; then
    echo "FAIL: control $c was PROVED. A false contract went through."
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
  rm -rf "$work/verification/creusot/target" "$work/verification/creusot/verif"
  # The fixtures the unit tests include_str! are not needed: tests are not built.
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
  if ! (cd "$work/verification/creusot" && cargo creusot --only=coma) >"$log/mutant-$id-coma.log" 2>&1; then
    echo "FAIL: mutant $id did not translate to Coma; a refusal would prove nothing"
    fail=1; rm -rf "$work"; continue
  fi
  if (cd "$work/verification/creusot" && cargo creusot --only=prove) >"$log/mutant-$id.log" 2>&1; then
    echo "FAIL: mutant $id ($fn) was PROVED. The contracts do not pin the code."
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
echo "CREUSOT GATE: GREEN (proofs pass; ${#controls[@]} controls and every mutant refused)"
