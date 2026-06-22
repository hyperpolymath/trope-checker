# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# Trope-particularity verification recipes. Imported by the root Justfile via
#   import? "build/just/trope.just"
# These are the trope-checker's real `check`/`test` targets (the RSR-template
# build/test/quality recipes remain generic stubs).

# Run all trope-particularity checks: schema + verified core + conformance.
check: trope-check

trope-check: trope-schema trope-idris trope-conformance
    @echo "trope-checker: all checks green"

# Validate the Trope IR JSON Schema and its positive/negative fixtures.
trope-schema:
    python3 tests/conformance/validate_schema.py

# Typecheck the Idris2 verified core (no axioms).
trope-idris:
    cd verification/proofs/idris2 && idris2 --typecheck trope.ipkg

# Run the machine conformance suite (IR -> verdict, with witnesses).
trope-conformance:
    python3 tests/conformance/run.py

# Regenerate the conformance fixtures (re-verifies each against the checker).
trope-fixtures:
    python3 tests/conformance/build_fixtures.py
