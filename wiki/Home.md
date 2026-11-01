<!-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk> -->
<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
# trope-checker wiki

The trope-particularity checker: a portable IR + checker for the honest/deceptive
**trope grade**, backed by machine-checked proofs across Idris2, Lean 4 + Mathlib, and
Agda.

## Verification streams

- **Verified core** (Idris2) — `verification/proofs/idris2/`: the grade algebra reused by
  the executable checker; the thing that runs is the thing that is proved.
- **Grade-algebra ground truth** (Lean 4 + Mathlib) — `verification/proofs/lean4/grade-boundary/`:
  the ratified commutative `GradeR` monoid (the historical carrier is non-commutative),
  full-carrier conicality, and the three-tier strict honest/deceptive cancellation
  boundary. Sorry-free; axioms `propext`/`Classical.choice`/`Quot.sound` only.
- **Tropical factorisation probe** (Lean 4 + Mathlib) — `verification/proofs/lean4/grade-factorisation/`:
  see [Tropical Factorisation Probe](Tropical-Factorisation-Probe.md). Ratified-carrier verdict
  *(B′) FACTORS AND VERIDICALITY-SIGHTED*; historical (B) applies to the
  pre-ratification carrier. A precondition only.
- **Calculus metatheory — Theorem B** (Agda `--safe --without-K`) — `verification/proofs/agda/theorem-b/`:
  intrinsic graded calculus, value substitution, β/let subject reduction, Honest
  Generation. Zero postulates. (`fix`/lfp open — CO-1.)

## The central open problem

**CO-1** — an operational model for `fix`/routing dynamics has been designed, but
not yet mechanised; full subject reduction remains open (issue #10). **O4**, the
limit-carrier question (issue #12), is resolved under the ratified carrier repair
and no longer gates CO-1. See `spec/notes/2026-07-07-co1-operational-model.adoc`
and `spec/notes/2026-07-07-l4-boundary-and-atoms.adoc` §4.

## Gates

```sh
just verify-all   # both Lean developments + Theorem B (Agda) + honesty gate
just build-lean   # grade-boundary + grade-factorisation + axiom audits
just build-agda   # Theorem B (--safe --without-K)
```

## Honesty

Status is ground-truthed by running the tools, not by reading prose. See
`AFFIRMATION.adoc` (dated snapshot), `AUDIT.adoc` (release gate), and
`docs/status/PROOF-NEEDS.adoc` (the proof ledger).
