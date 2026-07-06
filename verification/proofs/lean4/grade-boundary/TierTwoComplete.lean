-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
import GradeBoundary

/-!
# Exhaustive tier-2 membership (issue #14, OPEN-C) — and the full cancellation classification

`GradeBoundary.lean` proves *representative* tier-2 (honest, non-cancellative)
elements: `Predicated`, `Severed`, `Total`. Issue #14 asks for the remaining
claimed members, `Withheld` (bond) and `Fused` (merge). This file proves those
two, then goes further and *classifies* left-cancellation on every coordinate
and on the full grade carrier:

* `Bond.withheld_honest_not_cancel`, `Merge.fused_honest_not_cancel` — the two
  lemmas #14 asks for, same pattern as the existing `*_honest_not_cancel`.
* `Fate.atten_not_cancel` — a sharpening: even honest *finite* attenuation is
  non-cancellative **as a Fate element**, because `present` and `atten (Q 0)`
  are distinct yet composition cannot separate them
  (`atten d ▷ present = atten d = atten d ▷ atten (Q 0)`).
* `Fate.leftCancelWitness` / `Bond.leftCancelWitness` / `Merge.leftCancelWitness`
  — for every non-unit element of each coordinate, an explicit witness that
  left-cancellation fails.
* `Grade.grade_leftCancel_iff` — **the classification**: an element of the grade
  monoid is left-cancellative *iff it is the unit ε*.

The last theorem sharpens Deliverable 3 of `GradeBoundary.lean`: the "tier-1
cancellative core" (`honest_fidelity_cancel`) lives inside the fidelity
*dimension* `Delta` — the additive submonoid `Q ℕ ≅ (ℕ,+,0)` — and does **not**
lift to any non-unit element of the grade monoid itself, because the fidelity
dimension sits under the `atten` head, whose composition also has to answer for
`present` (and `atten (Q 0)` collides with it). Tier 1 at the `Grade` level is
exactly `{ε}`; the ℕ-core cancels only *within* fidelity.

**Quotient caveat (a discovered spec/carrier discrepancy, #13-adjacent).**
Spec v0.1 §3.1 declares `Attenuated(0) = Present`, but the carrier
(`Coords.idr`, and this mirror) keeps them *distinct values* — no quotient or
normalization is imposed anywhere. The classification below is a theorem about
the carrier as implemented. If the §3.1 identification were imposed (normalize
`Atten (Q 0) → Present`), the collision witness behind `atten_not_cancel`
disappears, honest *finite* attenuation becomes cancellative, and tier 1 at the
grade level is exactly the original "finite-fidelity + units" core of
`GradeBoundary.lean`. So the two statements of tier 1 — `{ε}` versus
"finite-fidelity + units" — are *both* right, about two different carriers, and
which one the calculus means is an open reconciliation question the spec should
settle. All witnesses below other than `atten_not_cancel` are chosen to be
robust under either reading.
-/

namespace Trope

/-! ## The two lemmas issue #14 asks for -/

namespace Bond

/-- **#14 (bond half).** `Withheld` is honest (not the deceptive `Misbound`) yet
non-cancellative: it absorbs the difference between `Intact` and `Withheld`. -/
theorem withheld_honest_not_cancel :
    withheld * intact = withheld * withheld ∧ (intact ≠ withheld) :=
  ⟨rfl, by decide⟩

/-- Every non-unit bond fails left-cancellation (unit = `Intact`). -/
theorem leftCancelWitness :
    ∀ b : Bond, b ≠ intact → ∃ x y : Bond, b * x = b * y ∧ x ≠ y := by
  intro b hb
  cases b with
  | intact => exact absurd rfl hb
  | withheld => exact ⟨intact, withheld, withheld_honest_not_cancel⟩
  | severed => exact ⟨intact, withheld, severed_honest_not_cancel⟩
  | misbound => exact ⟨intact, withheld, by decide⟩

/-- `Intact` (the unit) is left-cancellative. -/
theorem intact_leftCancel : ∀ x y : Bond, intact * x = intact * y → x = y := by
  intro x y h; simpa using h

end Bond

namespace Merge

/-- **#14 (merge half).** `Fused` is honest (the faithful, tagged collapse — not
the deceptive `Conflated`) yet non-cancellative: it absorbs the difference
between `Single` and `Fused`. -/
theorem fused_honest_not_cancel :
    fused * single = fused * fused ∧ (single ≠ fused) :=
  ⟨rfl, by decide⟩

/-- Every non-unit merge fails left-cancellation (unit = `Single`). -/
theorem leftCancelWitness :
    ∀ m : Merge, m ≠ single → ∃ x y : Merge, m * x = m * y ∧ x ≠ y := by
  intro m hm
  cases m with
  | single => exact absurd rfl hm
  | fused => exact ⟨single, fused, fused_honest_not_cancel⟩
  | conflated => exact ⟨single, fused, by decide⟩

/-- `Single` (the unit) is left-cancellative. -/
theorem single_leftCancel : ∀ x y : Merge, single * x = single * y → x = y := by
  intro x y h; simpa using h

end Merge

/-! ## The fate sharpening: honest finite attenuation is not cancellative either -/

namespace Fate

/-- Even honest finite attenuation fails left-cancellation as a `Fate` element:
`atten d ▷ present = atten d = atten d ▷ atten (Q 0)`, but
`present ≠ atten (Q 0)`. (The ℕ-core cancellativity of `GradeBoundary.lean`'s
`honest_fidelity_cancel` is a fact about the fidelity dimension `Delta`, not
about `Fate`: the `atten` head cannot separate `present` from zero-loss
attenuation.) -/
theorem atten_not_cancel (d : Delta) :
    atten d * present = atten d * atten (Delta.Q 0) ∧ (present ≠ atten (Delta.Q 0)) := by
  constructor
  · show comp (atten d) present = comp (atten d) (atten (Delta.Q 0))
    simp [comp, Delta.Q_zero]
  · intro h; exact Fate.noConfusion h

/-- Every non-unit fate fails left-cancellation (unit = `Present`). -/
theorem leftCancelWitness :
    ∀ f : Fate, f ≠ present → ∃ x y : Fate, f * x = f * y ∧ x ≠ y := by
  intro f hf
  cases f with
  | present => exact absurd rfl hf
  | atten d =>
      -- carrier-level witness; collapses under the §3.1 quotient (see module doc)
      exact ⟨present, atten (Delta.Q 0), atten_not_cancel d⟩
  | predicated =>
      -- quotient-robust: `predicated ▷ present = predicated = predicated ▷ predicated`
      exact ⟨present, predicated, ⟨rfl, by intro h; exact Fate.noConfusion h⟩⟩
  | dropped =>
      exact ⟨present, predicated, ⟨rfl, by intro h; exact Fate.noConfusion h⟩⟩
  | falsified =>
      exact ⟨present, predicated, ⟨rfl, by intro h; exact Fate.noConfusion h⟩⟩

/-- `Present` (the unit) is left-cancellative. -/
theorem present_leftCancel : ∀ x y : Fate, present * x = present * y → x = y := by
  intro x y h; simpa using h

end Fate

/-! ## The classification at the grade level: cancellative ⇔ unit -/

namespace Grade

/-- Lift a fate counterexample on the `fQuality` coordinate to the grade level,
padding every other coordinate with its unit so the products agree there. -/
private theorem lift_fQuality (g : Grade)
    (hw : ∃ x y : Fate, g.fQuality * x = g.fQuality * y ∧ x ≠ y) :
    ∃ x y : Grade, g * x = g * y ∧ x ≠ y := by
  obtain ⟨xf, yf, hxy, hne⟩ := hw
  refine ⟨⟨xf, .present, .present, .present, .intact, .single⟩,
          ⟨yf, .present, .present, .present, .intact, .single⟩, ?_, ?_⟩
  · show gcomp g _ = gcomp g _
    simp [gcomp, hxy]
  · intro h
    exact hne (congrArg Grade.fQuality h)

private theorem lift_fBearer (g : Grade)
    (hw : ∃ x y : Fate, g.fBearer * x = g.fBearer * y ∧ x ≠ y) :
    ∃ x y : Grade, g * x = g * y ∧ x ≠ y := by
  obtain ⟨xf, yf, hxy, hne⟩ := hw
  refine ⟨⟨.present, xf, .present, .present, .intact, .single⟩,
          ⟨.present, yf, .present, .present, .intact, .single⟩, ?_, ?_⟩
  · show gcomp g _ = gcomp g _
    simp [gcomp, hxy]
  · intro h
    exact hne (congrArg Grade.fBearer h)

private theorem lift_fContext (g : Grade)
    (hw : ∃ x y : Fate, g.fContext * x = g.fContext * y ∧ x ≠ y) :
    ∃ x y : Grade, g * x = g * y ∧ x ≠ y := by
  obtain ⟨xf, yf, hxy, hne⟩ := hw
  refine ⟨⟨.present, .present, xf, .present, .intact, .single⟩,
          ⟨.present, .present, yf, .present, .intact, .single⟩, ?_, ?_⟩
  · show gcomp g _ = gcomp g _
    simp [gcomp, hxy]
  · intro h
    exact hne (congrArg Grade.fContext h)

private theorem lift_fRecord (g : Grade)
    (hw : ∃ x y : Fate, g.fRecord * x = g.fRecord * y ∧ x ≠ y) :
    ∃ x y : Grade, g * x = g * y ∧ x ≠ y := by
  obtain ⟨xf, yf, hxy, hne⟩ := hw
  refine ⟨⟨.present, .present, .present, xf, .intact, .single⟩,
          ⟨.present, .present, .present, yf, .intact, .single⟩, ?_, ?_⟩
  · show gcomp g _ = gcomp g _
    simp [gcomp, hxy]
  · intro h
    exact hne (congrArg Grade.fRecord h)

private theorem lift_bond (g : Grade)
    (hw : ∃ x y : Bond, g.bond * x = g.bond * y ∧ x ≠ y) :
    ∃ x y : Grade, g * x = g * y ∧ x ≠ y := by
  obtain ⟨xb, yb, hxy, hne⟩ := hw
  refine ⟨⟨.present, .present, .present, .present, xb, .single⟩,
          ⟨.present, .present, .present, .present, yb, .single⟩, ?_, ?_⟩
  · show gcomp g _ = gcomp g _
    simp [gcomp, hxy]
  · intro h
    exact hne (congrArg Grade.bond h)

private theorem lift_merge (g : Grade)
    (hw : ∃ x y : Merge, g.merge * x = g.merge * y ∧ x ≠ y) :
    ∃ x y : Grade, g * x = g * y ∧ x ≠ y := by
  obtain ⟨xm, ym, hxy, hne⟩ := hw
  refine ⟨⟨.present, .present, .present, .present, .intact, xm⟩,
          ⟨.present, .present, .present, .present, .intact, ym⟩, ?_, ?_⟩
  · show gcomp g _ = gcomp g _
    simp [gcomp, hxy]
  · intro h
    exact hne (congrArg Grade.merge h)

/-- **The cancellation classification (carrier-level).** An element of the
grade monoid *as implemented* is left-cancellative **iff** it is the unit ε.
Tier 1 at the grade level is exactly `{ε}`; tier 2 (honest) and tier 3
(deceptive) jointly exhaust every other element. Combined with
`leftCancelWitness` on each coordinate this makes tier-2 membership exhaustive
— closing OPEN-C beyond the representatives. Under the spec's §3.1
`Attenuated(0) = Present` identification (not imposed by the carrier — see the
module docstring) the `atten` case of the proof would need, and would have, no
witness: finite attenuation joins tier 1 there. -/
theorem grade_leftCancel_iff (g : Grade) :
    (∀ x y : Grade, g * x = g * y → x = y) ↔ g = 1 := by
  constructor
  · intro hc
    by_contra hne
    -- some coordinate differs from its unit; produce a witness pair there
    have : ∃ x y : Grade, g * x = g * y ∧ x ≠ y := by
      by_cases hq : g.fQuality = .present
      · by_cases hbr : g.fBearer = .present
        · by_cases hcx : g.fContext = .present
          · by_cases hr : g.fRecord = .present
            · by_cases hbo : g.bond = .intact
              · by_cases hm : g.merge = .single
                · exfalso
                  apply hne
                  cases g
                  simp only at hq hbr hcx hr hbo hm
                  simp [one_def, epsilon, hq, hbr, hcx, hr, hbo, hm]
                · exact lift_merge g (Merge.leftCancelWitness _ hm)
              · exact lift_bond g (Bond.leftCancelWitness _ hbo)
            · exact lift_fRecord g (Fate.leftCancelWitness _ hr)
          · exact lift_fContext g (Fate.leftCancelWitness _ hcx)
        · exact lift_fBearer g (Fate.leftCancelWitness _ hbr)
      · exact lift_fQuality g (Fate.leftCancelWitness _ hq)
    obtain ⟨x, y, hxy, hne'⟩ := this
    exact hne' (hc x y hxy)
  · rintro rfl
    intro x y h
    cases x; cases y
    simpa [mul_def, gcomp, one_def, epsilon, Grade.mk.injEq] using h

end Grade

end Trope

/-! ## Axiom audit (sorry-free check) -/
section AxiomAudit
open Trope
#print axioms Trope.Bond.withheld_honest_not_cancel
#print axioms Trope.Merge.fused_honest_not_cancel
#print axioms Trope.Fate.atten_not_cancel
#print axioms Trope.Fate.leftCancelWitness
#print axioms Trope.Bond.leftCancelWitness
#print axioms Trope.Merge.leftCancelWitness
#print axioms Trope.Grade.grade_leftCancel_iff
end AxiomAudit
