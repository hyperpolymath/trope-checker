# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# FORMAL VERIFICATION (PROOFS)
#
# Imported by ../../Justfile via `import? "build/just/proofs.just"`.
# Recipes here check formal proofs across Idris2, Lean4 and Agda, plus
# scan for dangerous/unsafe constructs and report status. Run via
# `just proof-check-all` for the full sweep.

# Check all formal proofs (Idris2 + Lean4 + Agda)
proof-check-all: proof-check-idris2 proof-check-lean4 proof-check-agda proof-scan-dangerous
    @echo "=== All proof checks complete ==="

# Check Idris2 proofs by PACKAGE (the verified core + the ABI seam)
#
# This recipe used to `find` every .idr under verification/ and run
# `idris2 --check` on each from the repo root — where module names do not
# resolve, template files that belong to no package fail spuriously, and a
# missing toolchain reported SKIP/exit 0, i.e. success. It was red on main
# for exactly those reasons (noted in PR #102). A package typecheck is the
# check that means something: it is what CI runs, with %default total
# enforced by the modules themselves. A missing toolchain is a FAIL here:
# a gate that passes when it did not run is worse than no gate.
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

# Check Lean4 proofs by PACKAGE (lake build at CI strictness)
#
# Was: `lean <file>` per file from the root (imports unresolvable, so
# permanently red) plus SKIP-on-missing-toolchain. Now the same build CI
# runs: both lake packages with warnings as errors.
proof-check-lean4:
    #!/usr/bin/env bash
    set -euo pipefail
    echo "=== Checking Lean4 proofs (lake build --wfail, both packages) ==="
    if ! command -v lake &>/dev/null; then
        echo "FAIL: lake not installed (Lean v4.16.0, see lean-toolchain files) — refusing to report a skip as a pass"
        exit 1
    fi
    ( cd verification/proofs/lean4/grade-boundary && lake build --wfail )
    ( cd verification/proofs/lean4/grade-factorisation && lake build --wfail )
    # Orphan guard: every .lean in the tree must be a lean_lib of one of
    # the two lakefiles (a file no package builds is never kernel-checked).
    orphans=""
    for f in $(find verification/proofs/lean4 -name '*.lean' -not -path '*/.lake/*' | sort); do
        base="$(basename "$f" .lean)"
        grep -qhE '^name = "'"$base"'"' verification/proofs/lean4/*/lakefile.toml \
          || orphans="$orphans $f"
    done
    if [ -n "$orphans" ]; then
        echo "FAIL: Lean files belonging to no lake package (never built):$orphans"
        exit 1
    fi
    echo "PASS: both Lean packages build (--wfail); no orphan .lean files"

# Check Agda proofs (same entry point and flags as build-agda / CI)
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

# (No proof-check-coq: the tree carries no Coq — T5 of PR #102 removed the
# never-instantiated template, and a recipe whose find matches nothing and
# whose missing toolchain exits 0 is, in ADR 0005's words, "a gate that
# cannot fail". If Coq ever lands for real, add the recipe with the proof.)

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

# Show proof status summary
proof-status:
    #!/usr/bin/env bash
    echo "=== Proof Status ==="
    echo ""
    echo "Idris2: $(find verification/proofs/idris2 -name '*.idr' 2>/dev/null | wc -l) files"
    echo "Lean4:  $(find verification/proofs/lean4 -name '*.lean' 2>/dev/null | wc -l) files"
    echo "Agda:   $(find verification/proofs/agda -name '*.agda' 2>/dev/null | wc -l) files"
    echo ""
    # PROOF-STATUS may live at root, docs/status/ (post-#20), .md or .adoc (post-#23)
    for candidate in docs/status/PROOF-STATUS.adoc docs/status/PROOF-STATUS.md PROOF-STATUS.adoc PROOF-STATUS.md; do
        if [ -f "$candidate" ]; then
            grep -E "^\| \*\*Total\*\*|^\| \*Total\*" "$candidate" 2>/dev/null || echo "(No summary row in $candidate)"
            exit 0
        fi
    done
    echo "(No PROOF-STATUS file found at root or docs/status/)"

# ---------------------------------------------------------------------------
# Theorem-B integration targets (the grade-algebra ground truth + its Agda
# metatheory). These supersede the naïve per-file `proof-check-{lean4,agda}`
# for the two pinned developments, which need lake+Mathlib (Lean) and
# `--without-K` over an `All.agda` entry point (Agda) rather than a bare
# per-file check.
# ---------------------------------------------------------------------------

# Build BOTH Lean packages and axiom-audit every `#print axioms` receipt.
#
# The old "audit" re-ran `lake build | grep ... || true` on a warm tree:
# lake re-emits nothing for up-to-date modules, grep found nothing, and the
# step passed having audited zero theorems. Now each source is re-elaborated
# with `lake env lean`, its #print axioms output is captured, and EVERY
# reported axiom set is checked against the allowlist {propext,
# Classical.choice, Quot.sound} — with a non-vacuity floor (the corpus
# carries 70+ receipts today; the audit fails below 50 rather than passing
# on an empty grep).
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
# Build both formal developments + run the Lean source honesty gate (the merge gate).
verify-all: build-lean build-agda
    #!/usr/bin/env bash
    set -euo pipefail
    echo "=== verify-all: Lean source honesty gate ==="
    # Every Lean source (mirrors proofs.yml lean-source-honesty; keep the two in step).
    for f in $(git ls-files 'verification/proofs/lean4/*.lean' 'verification/proofs/lean4/*/*.lean'); do
        echo "--- gating $f ---"
        # Comment-aware, token-based (mirrors proofs.yml; keep the two in step).
        stripped=$(awk -f tests/lib/strip-proof-comments.awk "$f")
        if grep -nE '(^|[^[:alnum:]_.])(sorry|admit|unsafe)([^[:alnum:]_]|$)|\bnative_decide\b|\bsorryAx\b|\bofReduceBool\b|\bextern\b|\bimplemented_by\b' <<<"$stripped"; then
            echo "FAIL: forbidden Lean construct (sorry/admit/native_decide/sorryAx/ofReduceBool/unsafe/extern/implemented_by) in $f"; exit 1; fi
        if grep -nE '^[[:space:]]*axiom\b' <<<"$stripped"; then
            echo "FAIL: user axiom declared in $f"; exit 1; fi
    done
    echo "PASS: verify-all — Lean green & axiom-clean; Agda strict-flags green."
