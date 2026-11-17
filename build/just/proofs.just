# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# FORMAL VERIFICATION (PROOFS)
#
# Imported by ../../Justfile via `import? "build/just/proofs.just"`.
# Recipes here check the four proof developments in the roles ADR 0005 D4
# gives them (as amended 2026-11-17): Agda is the normative kernel; Rocq and
# core Lean (no Mathlib) are the PROOF-POLICY §2 recheck legs; Lean + Mathlib
# is a generator, never a leg; Idris2 is the executable reference. They also
# scan for dangerous/unsafe constructs and report status. Run via
# `just proof-check-all` for the full sweep.

# Check all formal proofs (Agda kernel, Rocq + core-Lean recheck legs, Lean + Mathlib generator, Idris2 reference)
proof-check-all: proof-check-idris2 proof-check-lean4 proof-check-agda recheck-legs proof-scan-dangerous
    @echo "=== All proof checks complete ==="

# This recipe used to `find` every .idr under verification/ and run
# `idris2 --check` on each from the repo root — where module names do not
# resolve, template files that belong to no package fail spuriously, and a
# missing toolchain reported SKIP/exit 0, i.e. success. It was red on main
# for exactly those reasons (noted in PR #102). A package typecheck is the
# check that means something: it is what CI runs, with %default total
# enforced by the modules themselves. A missing toolchain is a FAIL here:
# a gate that passes when it did not run is worse than no gate.
#
# Check the Idris2 executable reference by PACKAGE (the verified core + the ABI seam; off the PWG ladder)
proof-check-idris2:
    #!/usr/bin/env bash
    set -euo pipefail
    echo "=== Checking Idris2 proofs (package typechecks) ==="
    if ! command -v idris2 &>/dev/null; then
        echo "FAIL: idris2 not installed (need 0.8.0, see .mise.toml) — refusing to report a skip as a pass"
        exit 1
    fi
    ( cd verification/proofs/idris2 && idris2 --typecheck trope.ipkg )
    idris2 --typecheck abi.ipkg
    # Orphan guard: every .idr in the proof tree must be a module of
    # trope.ipkg. A file no package builds is a status surface that lies.
    orphans=""
    for f in $(find verification/proofs/idris2 -name '*.idr' | sort); do
        mod="${f#verification/proofs/idris2/}"; mod="${mod%.idr}"; mod="${mod//\//.}"
        grep -qE "(^|[[:space:],])${mod}([[:space:],]|$)" verification/proofs/idris2/trope.ipkg \
          || orphans="$orphans $f"
    done
    if [ -n "$orphans" ]; then
        echo "FAIL: Idris2 files belonging to no package (never typechecked):$orphans"
        exit 1
    fi
    echo "PASS: trope.ipkg + abi.ipkg typecheck; no orphan .idr files"

# Was: `lean <file>` per file from the root (imports unresolvable, so
# permanently red) plus SKIP-on-missing-toolchain. Now the same build CI
# runs: both lake packages with warnings as errors. These are the GENERATOR
# (ADR 0005 D4 as amended), never a §2 leg; the core-Lean recheck leg is
# proof-check-lean-core.
#
# Check the Lean + Mathlib generator packages by PACKAGE (lake build --wfail; a generator, never a §2 leg)
proof-check-lean4:
    #!/usr/bin/env bash
    set -euo pipefail
    echo "=== Checking Lean + Mathlib generator (lake build --wfail, both packages) ==="
    if ! command -v lake &>/dev/null; then
        echo "FAIL: lake not installed (Lean v4.16.0, see lean-toolchain files) — refusing to report a skip as a pass"
        exit 1
    fi
    ( cd verification/proofs/lean4/grade-boundary && lake build --wfail )
    ( cd verification/proofs/lean4/grade-factorisation && lake build --wfail )
    # Orphan guard: every .lean in the tree must be a lean_lib of one of
    # the two lakefiles, or be THE core-Lean leg that
    # scripts/check-recheck-legs.sh gates (proof-check-lean-core). A file
    # neither builds is never kernel-checked.
    leg="$(sed -n 's/^LEAN_FILE="\(.*\)"$/\1/p' scripts/check-recheck-legs.sh)"
    [ -n "$leg" ] || { echo "FAIL: no LEAN_FILE in scripts/check-recheck-legs.sh — cannot tell the core-Lean leg from an orphan"; exit 1; }
    orphans=""
    for f in $(find verification/proofs/lean4 -name '*.lean' -not -path '*/.lake/*' | sort); do
        [ "$f" = "$leg" ] && continue
        base="$(basename "$f" .lean)"
        grep -qhE '^name = "'"$base"'"' verification/proofs/lean4/*/lakefile.toml \
          || orphans="$orphans $f"
    done
    if [ -n "$orphans" ]; then
        echo "FAIL: Lean files belonging to no lake package and not the core-Lean leg (never checked):$orphans"
        exit 1
    fi
    echo "PASS: both Lean + Mathlib packages build (--wfail); no orphan .lean files (core-Lean leg: $leg)"

# Check the Agda normative kernel (same entry point and flags as build-agda / CI)
proof-check-agda:
    #!/usr/bin/env bash
    set -euo pipefail
    echo "=== Checking Agda proofs (Theorem B, strictest flags) ==="
    if ! command -v agda &>/dev/null; then
        echo "FAIL: agda not installed (need 2.7.0.1 + stdlib 2.0) — refusing to report a skip as a pass"
        exit 1
    fi
    AGDA_FLAGS=(--safe --without-K --cubical-compatible)  # --exact-split/-Werror live in theorem-b OPTIONS + .agda-lib flags (CLI forms would leak into stdlib compilation)
    ( cd verification/proofs/agda/theorem-b \
        && agda "${AGDA_FLAGS[@]}" All.agda \
        && agda "${AGDA_FLAGS[@]}" Smoke.agda )
    echo "PASS: Theorem B typechecks (${AGDA_FLAGS[*]})"

# ---------------------------------------------------------------------------
# PROOF-POLICY §2 recheck legs: Rocq and core Lean (ADR 0005 D4/D5, as
# amended 2026-11-17). T5 of PR #102 removed a never-instantiated Coq
# template and its silently-skipping recipe, "a gate that cannot fail", and
# said a Coq recipe should come back only with a real proof. The Rocq
# development that landed on 2026-11-17 is that proof, an instantiated leg,
# and the recipes below check it. The gate is
# scripts/check-recheck-legs.sh, the same script the proofs.yml
# `recheck-legs` job runs. It asserts the pinned prover version (Coq 8.18.0,
# Lean 4.16.0), and a missing prover FAILS (it never skips). It also fails
# on any axiom and on an empty audit domain.
# ---------------------------------------------------------------------------

# Rocq recheck leg: compile, then `Print Assumptions` on every Theorem and Lemma
proof-check-rocq:
    #!/usr/bin/env bash
    set -euo pipefail
    # Orphan guard: the script gates ONE Rocq file. Any other .v in the proof
    # tree would be a development no gate checks.
    leg="$(sed -n 's/^ROCQ_FILE="\(.*\)"$/\1/p' scripts/check-recheck-legs.sh)"
    [ -n "$leg" ] || { echo "FAIL: no ROCQ_FILE in scripts/check-recheck-legs.sh"; exit 1; }
    orphans=""
    for f in $(find verification/proofs -name '*.v' -not -path '*/_build/*' | sort); do
        [ "$f" = "$leg" ] || orphans="$orphans $f"
    done
    if [ -n "$orphans" ]; then
        echo "FAIL: Rocq files no gate checks (only $leg is gated):$orphans"
        exit 1
    fi
    bash scripts/check-recheck-legs.sh rocq

# Core-Lean recheck leg (no Mathlib): check, then collectAxioms on every declared theorem
proof-check-lean-core:
    @bash scripts/check-recheck-legs.sh lean

# Planted controls: Admitted, sorry, a user axiom, an empty domain and a definition drift must each be caught
proof-check-recheck-controls:
    @bash scripts/check-recheck-legs.sh controls

# Both §2 recheck legs plus their planted controls (mirrors the proofs.yml recheck-legs job)
recheck-legs: proof-check-rocq proof-check-lean-core proof-check-recheck-controls
    @echo "PASS: recheck-legs — Rocq and core-Lean legs green, every planted control caught"

# Scan for dangerous patterns in proof files (believe_me, sorry, Admitted, etc.)
# COMMENT-AWARE: strips line (-- //) and block ({- -}, /- -/, (* *)) comments before
# matching, so honest convention prose ("no postulate", "sorry-free") is NOT flagged
# (line numbers preserved). Excludes vendored deps (.lake/, _build/). Verified to still
# catch genuine constructs — do not "simplify" back to a bare word-grep.
proof-scan-dangerous:
    #!/usr/bin/env bash
    set -euo pipefail
    echo "=== Scanning for dangerous patterns in proofs (comment-aware) ==="
    DANGEROUS=0
    PATTERNS="believe_me|assert_total|postulate|sorry|Admitted|unsafeCoerce|Obj\.magic"
    for f in $(find verification/proofs \( -name '*.idr' -o -name '*.lean' -o -name '*.agda' -o -name '*.v' \) \
                -not -path '*/.lake/*' -not -path '*/_build/*' 2>/dev/null); do
        MATCHES=$(perl -0777 -pe '
            s{\{-.*?-\}}{ $& =~ tr/\n//cdr }ges;     # Agda block comment
            s{/-.*?-/}{ $& =~ tr/\n//cdr }ges;       # Lean block comment
            s{\(\*.*?\*\)}{ $& =~ tr/\n//cdr }ges;    # Coq block comment
          ' "$f" 2>/dev/null | sed -E 's,(--|//).*,,' | grep -nE "$PATTERNS" || true)
        if [ -n "$MATCHES" ]; then
            echo "  DANGEROUS: $f"
            echo "$MATCHES" | sed 's/^/    /'
            DANGEROUS=$((DANGEROUS + 1))
        fi
    done
    if [ "$DANGEROUS" -gt 0 ]; then
        echo "FAIL: $DANGEROUS file(s) contain dangerous patterns"
        exit 1
    fi
    echo "PASS: No dangerous patterns found in proofs (comments excluded)"

# Show proof status summary: the four developments by ADR 0005 D4 role, then the PWG census
proof-status:
    #!/usr/bin/env bash
    set -uo pipefail
    # Source files only: never count a .lake/ or _build/ tree (vendored Mathlib).
    n() { find "$@" -not -path '*/.lake/*' -not -path '*/_build/*' 2>/dev/null | wc -l; }
    L=verification/proofs/lean4
    echo "=== Proof Status (roles: ADR 0005 D4, as amended 2026-11-17) ==="
    echo ""
    # The role goes last: printf pads by bytes, and "§" is two of them.
    printf '%-13s %5s  %-27s %s\n' \
      "Development"  "Files" "Gate"                       "Role" \
      "Agda"         "$(n verification/proofs/agda -name '*.agda')"  "just proof-check-agda"      "normative kernel" \
      "Rocq"         "$(n verification/proofs/rocq -name '*.v')"      "just proof-check-rocq"      "§2 recheck leg" \
      "Lean (core)"  "$(n "$L/ratified-order" -name '*.lean')"        "just proof-check-lean-core" "§2 recheck leg, no Mathlib" \
      "Lean+Mathlib" "$(n "$L/grade-boundary" "$L/grade-factorisation" -name '*.lean')" "just proof-check-lean4" "generator, never a leg" \
      "Idris2"       "$(n verification/proofs/idris2 -name '*.idr')"  "just proof-check-idris2"    "executable reference, off the PWG ladder"
    echo ""
    echo "Proof Witness Grades are derived from verification/pwg.json (PROOF-POLICY §8.4 rule 2):"
    bash scripts/pwg-derive.sh --census

# ---------------------------------------------------------------------------
# Theorem-B integration targets (the grade-algebra ground truth + its Agda
# metatheory). These supersede the naïve per-file `proof-check-{lean4,agda}`
# for the two pinned developments, which need lake+Mathlib (Lean) and
# `--without-K` over an `All.agda` entry point (Agda) rather than a bare
# per-file check. verify-all, the merge gate, also runs the §2 recheck legs
# (recheck-legs, above), so all four proof developments gate a merge.
# ---------------------------------------------------------------------------

# The old "audit" re-ran `lake build | grep ... || true` on a warm tree:
# lake re-emits nothing for up-to-date modules, grep found nothing, and the
# step passed having audited zero theorems. Now each source is re-elaborated
# with `lake env lean`, its #print axioms output is captured, and EVERY
# reported axiom set is checked against the allowlist {propext,
# Classical.choice, Quot.sound} — with a non-vacuity floor (the corpus
# carries 70+ receipts today; the audit fails below 50 rather than passing
# on an empty grep).
#
# Build BOTH Lean + Mathlib generator packages and axiom-audit every `#print axioms` receipt.
build-lean:
    #!/usr/bin/env bash
    set -euo pipefail
    ROOT="$(pwd)"
    # Build the package named by $1 under verification/proofs/lean4 and check
    # its reported axioms against propext, Classical.choice and Quot.sound.
    # Add its receipt count to TOTAL_RECEIPTS; build, re-elaboration or
    # axiom-allowlist failures terminate the recipe.
    audit_pkg() {
        local pkg="$1"
        echo "=== build-lean: ${pkg} (Lean 4 + Mathlib, pinned) ==="
        ( cd "$ROOT/verification/proofs/lean4/${pkg}" && lake build --wfail )
        local out receipts f
        out="$(mktemp)"
        for f in "$ROOT/verification/proofs/lean4/${pkg}"/*.lean; do
            ( cd "$ROOT/verification/proofs/lean4/${pkg}" && lake env lean "$f" ) >>"$out" 2>&1 \
              || { echo "FAIL: re-elaborating $f for the axiom audit failed"; cat "$out"; exit 1; }
        done
        receipts="$(grep -cE "depends on axioms|does not depend on any axioms" "$out" || true)"
        if grep -E "depends on axioms" "$out" | grep -vE "^.*depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]$" >/dev/null; then
            echo "FAIL: axiom outside the allowlist (propext / Classical.choice / Quot.sound):"
            grep -E "depends on axioms" "$out" | grep -vE "^.*depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]$"
            exit 1
        fi
        echo "axiom audit: ${receipts} receipts in ${pkg}, all within the allowlist"
        TOTAL_RECEIPTS=$((TOTAL_RECEIPTS + receipts))
        rm -f "$out"
    }
    TOTAL_RECEIPTS=0
    audit_pkg grade-boundary
    audit_pkg grade-factorisation
    if [ "$TOTAL_RECEIPTS" -lt 50 ]; then
        echo "FAIL: only ${TOTAL_RECEIPTS} axiom receipts audited (floor 50) — audit went vacuous"
        exit 1
    fi
    echo "PASS: build-lean — both packages build; ${TOTAL_RECEIPTS} axiom receipts audited, none outside the allowlist"

# `--safe` already guarantees no postulate / trustMe / TERMINATING, so this IS the Agda honesty gate.
#
# Typecheck the Theorem-B Agda metatheory (whole dev + headline pins) at full strictness.
build-agda:
    #!/usr/bin/env bash
    set -euo pipefail
    echo "=== build-agda: Theorem B metatheory (strictest flags) ==="
    # Needs Agda >= 2.7.0 and agda-stdlib >= 2.0 (Data.Product.Base, and
    # --cubical-compatible throughout stdlib); the CI job pins Agda 2.7.0.1 +
    # stdlib 2.0 by checksum — see proofs.yml agda-theorem-b. The same set
    # lives in theorem-b.agda-lib `flags:` and every module's OPTIONS pragma.
    AGDA_FLAGS=(--safe --without-K --cubical-compatible)  # --exact-split/-Werror live in theorem-b OPTIONS + .agda-lib flags (CLI forms would leak into stdlib compilation)
    cd verification/proofs/agda/theorem-b
    agda "${AGDA_FLAGS[@]}" All.agda
    agda "${AGDA_FLAGS[@]}" Smoke.agda
    echo "PASS: All.agda + Smoke.agda typecheck (${AGDA_FLAGS[*]}; --safe ⇒ postulate-free by construction)"

# (Agda postulate-freedom is enforced by --safe in build-agda; a word-grep would
# false-positive on the honest 'sorry-free' / 'No postulate' comments — do NOT use one.)
#
# The merge gate: Lean + Mathlib generator, Agda kernel, Rocq + core-Lean recheck legs and controls, Lean honesty gate, PWG record.
verify-all: build-lean build-agda recheck-legs
    #!/usr/bin/env bash
    set -euo pipefail
    echo "=== verify-all: Lean source honesty gate ==="
    # Every Lean source (mirrors proofs.yml lean-source-honesty; keep the two in step).
    for f in $(git ls-files 'verification/proofs/lean4/*.lean' 'verification/proofs/lean4/*/*.lean'); do
        echo "--- gating $f ---"
        # Comment-aware, token-based (mirrors proofs.yml; keep the two in step).
        stripped=$(awk -f tests/lib/strip-proof-comments.awk "$f")
        if grep -nE '(^|[^[:alnum:]_.])(sorry|admit|unsafe)([^[:alnum:]_]|$)|\bnative_decide\b|\bsorryAx\b|\bofReduceBool\b|\bextern\b|\bimplemented_by\b|\baddDecl\b|\baxiomDecl\b' <<<"$stripped"; then
            echo "FAIL: forbidden Lean construct (sorry/admit/native_decide/sorryAx/ofReduceBool/unsafe/extern/implemented_by/addDecl/axiomDecl) in $f"; exit 1; fi
        # Token-based, not line-initial (mirrors proofs.yml): `private axiom
        # foo` is an axiom declaration too, and this local gate must not be
        # weaker than the CI one it mirrors.
        if grep -nE '(^|[^[:alnum:]_.])axiom([^[:alnum:]_]|$)' <<<"$stripped"; then
            echo "FAIL: user axiom declared in $f"; exit 1; fi
    done
    echo "=== verify-all: Proof Witness Grade record ==="
    bash scripts/pwg-check.sh
    echo "PASS: verify-all — Lean + Mathlib green, no sorryAx and no user axiom; Agda strict-flags green; Rocq and core-Lean recheck legs green with every planted control caught; PWG record derived and in step."

# Derive every Proof Witness Grade from verification/pwg.json and show the census.
# The ledger holds EVIDENCE only; PROOF-POLICY §8.4 rule 2 says the grade is
# computed from it, never written by hand.
pwg:
    @bash scripts/pwg-derive.sh --census
    @echo
    @bash scripts/pwg-derive.sh --json | jq -r '.[] | "  \(.pwg)\t\(.id)\t\(.title)"'

# Regenerate the PWG table inside docs/status/PROOF-STATUS.adoc from the ledger.
# Rewrites only the region between the PWG-TABLE:BEGIN/END markers.
pwg-render:
    #!/usr/bin/env bash
    set -euo pipefail
    f=docs/status/PROOF-STATUS.adoc
    grep -q '^// PWG-TABLE:BEGIN' "$f" || { echo "FAIL: $f has no PWG-TABLE:BEGIN marker"; exit 1; }
    grep -q '^// PWG-TABLE:END'   "$f" || { echo "FAIL: $f has no PWG-TABLE:END marker"; exit 1; }
    tmp=$(mktemp)
    awk '/^\/\/ PWG-TABLE:BEGIN/{print; exit} {print}' "$f" > "$tmp"
    bash scripts/pwg-derive.sh --table >> "$tmp"
    awk 'f{print} /^\/\/ PWG-TABLE:END/{if(!f){print; f=1}}' "$f" >> "$tmp"
    mv "$tmp" "$f"
    echo "regenerated the PWG table in $f"

# 🔴 GATE: the ledger is well-formed, asserts no grade, and the published table
# and census are the derived ones. Falsified by scripts/test-gate-falsifiability.sh.
pwg-check:
    @bash scripts/pwg-check.sh
