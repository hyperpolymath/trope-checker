# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# Trope-particularity verification recipes (Idris2 through-and-through; no Python).
# Imported by the root Justfile via  import? "build/just/trope.just"

# Run everything: typecheck the verified core, build the checker, run conformance.
check: trope-proofs trope-build trope-conformance

# Typecheck the verified core (the proofs) — no axioms.
trope-proofs:
    cd verification/proofs/idris2 && idris2 --typecheck trope.ipkg

# Install the verified core as a package, then build the executable checker.
trope-build:
    idris2 --install verification/proofs/idris2/trope.ipkg
    cd src/idris2 && idris2 --build tropecheck.ipkg

# Machine conformance suite: IR -> verdict (+ witness) and schema-invalid rejection.
trope-conformance:
    bash tests/conformance/run.sh

# Convenience: run the checker on one IR document.
tropecheck ir:
    src/idris2/build/exec/tropecheck {{ir}}
