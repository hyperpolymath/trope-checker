<!-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk> -->
<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
# Tropical Factorisation Probe

A dynamics-free, purely algebraic probe: *does the trope grade admit a homomorphic
projection onto a commutative tropical cost, with all non-commutativity confined to the
complement?* Source: `verification/proofs/lean4/grade-factorisation/`; full write-up:
`verification/proofs/lean4/grade-factorisation/REPORT.adoc`.

## Verdict — (B′) FACTORS AND VERIDICALITY-SIGHTED (ratified carrier)

Under the ratified carrier (R-2026-07-07, ADR 0004 A1/A2), a nontrivial, surjective
monoid homomorphism `πR : (GradeR, ▷, ε) → (Δ, +, Q 0)` exists (`piR_hom`, `piR_one`,
`piRHom`, `piR_nontrivial`, `piR_surjective`). It distinguishes honest `Dropped`
from deceptive `Falsified`: `∞` (`total`) versus `⊤` (`unknown`), proved by
`phiR_sighted` and `piR_sighted` in `GradeFactorisationR.lean`.

This sightedness has a trade-off: attenuation payload `⊤` is squashed to `∞`, so
`Atten ∞` and `Atten ⊤` share a cost (`sighted_forces_squash`). `Predicated` and
`Dropped` also share the honest total-loss cost (`phiR_collapses_predicated_dropped`).
See the report's “Re-run under the ratified carrier” section for the full result.

## Historical verdict — (B) FACTORS but VERIDICALITY-BLIND (pre-ratification)

The following result applies only to the pre-ratification carrier, whose fate
composition has `Dropped ▷ Falsified = Dropped` and `Falsified ▷ Dropped = Falsified`.
The ratified carrier instead has `Dropped ▷ Falsified = Falsified`; the forced-collapse
claim below does not apply to it.

A **nontrivial** monoid homomorphism `π : (Grade, ▷, ε) → (Δ, +, Q 0)` onto the
commutative tropical fidelity carrier `Δ = WithTop (WithTop ℕ)` **exists** — but **every**
multiplicative map from `Fate` (and from `Grade`) into **any** commutative monoid is
**forced** to identify the honest `dropped` with the deceptive `falsified`. So the best
case (A, veridicality-preserving) is **impossible**, and the dead case (C, no
homomorphism) is **false**.

The blindness is **co-located** with the non-commutativity: it is the **fate-axis**
honest/deceptive distinction that collapses of necessity, because that coordinate has two
disagreeing absorbing heads. The **commutative** `Bond`/`Merge` coordinates carry no such
obstruction — their deceptions stay tropically separable.

## Historical proofs (Lean 4 + Mathlib; sorry-free; `propext`/`Quot.sound` only)

| Theorem | Statement |
| --- | --- |
| `pi_hom`, `pi_one`, `piHom` | `π` is a monoid homomorphism `Grade →* Multiplicative Δ`. |
| `pi_nontrivial`, `pi_surjective` | `π` separates attenuation levels and is onto `Δ` (not the trivial collapse). |
| `phiV_not_hom`, `piV_not_hom` | The veridicality-faithful candidate is **not** a homomorphism — breaker at `dropped ▷ falsified` (`total ≠ total + unknown = unknown`). |
| `forced_collapse_general`, `forced_collapse_grade` | **(axiom-free)** every multiplicative map into any commutative monoid identifies `dropped`/`falsified`. |
| `no_veridicality_faithful_hom` | Outcome (A) is impossible. |
| `psiBond_hom`, `psiBond_separates_honest_deceptive` | Bond deception **is** tropically separable — the loss is fate-specific. |
| `pi_blind_to_noncomm`, `grade_F2_noncomm`, `pi_collapses_F2` | `π` is blind to all non-commutativity; F2 confined to the complement. |

## Necessary-not-sufficient (read this)

A positive result means **only** "the commutative cost-quotient EXISTS — the tropical
route is NOT EXCLUDED, precondition met." It does **not** mean "tropical solves recursion."
Whether a fixpoint's grade actually lives in the commutative part needs an operational
model (**CO-1**, issue #10, gated by **O4**, issue #12) and stays parked. This probe can only
kill the tropical route or fail to kill it; it cannot confirm it. The fixpoint is **not**
solved, handled, or addressed by this work.

## Reproduce

```sh
cd verification/proofs/lean4/grade-factorisation
just build      # green; imports grade-boundary, reuses the pinned Mathlib build
just falsify    # sorry-free, axiom-clean; both falsifier witnesses live
just verdict    # names the load-bearing theorems
```

## Next stage

Issue #10 (CO-1 — operational model for `fix`/lfp), itself gated by issue #12 (O4 — the
limit carrier).
