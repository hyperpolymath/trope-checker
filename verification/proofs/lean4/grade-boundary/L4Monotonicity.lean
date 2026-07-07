-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
import GradeBoundary

/-!
# The L4 monotonicity boundary — where it fails, why, and a two-amendment repair

Spec v0.1 §4 states **L4**: ▷ is monotone in each argument w.r.t. the retention
order ⊑, and §7 uses L4 to justify the existence of `fix`'s least-fixed-point
grade (Knaster–Tarski needs a monotone functional on a complete lattice). The
Idris2 stream already recorded that *strict* L4 fails on the fate coordinate
(`Trope.Soundness.fateL4MonotonicityFails`). This file does three things:

1. **Localises the failure.** Machine-checked witnesses that L4 fails on the
   shipped carrier, in both arguments (`comp_not_monotone_right/left`), and that
   every witness passes through the same two design points:
   - the `{Predicated, Dropped}` antichain (the "duck check"), and
   - the clause `Dropped ▷ Falsified = Dropped` — an upstream *drop* erases a
     downstream *lie*.
2. **Diagnoses one clause.** `Dropped ▷ Falsified = Dropped` is simultaneously
   the *sole* source of the grade algebra's non-commutativity
   (`GradeBoundary.grade_mul_not_comm`'s witness is exactly this pair) and the
   falsify-side monotonicity failures — and it is in tension with L5's moral
   core, which wants deception infectious. An honest absorber should not
   launder a lie.
3. **Proves the repair.** The *amended* fate carrier `FateA` with exactly two
   changes:
   - **(A1)** `Dropped ▷ Falsified = Falsified` — the deceptive bottom becomes a
     two-sided zero (L5 strengthened to both sides);
   - **(A2)** `Dropped ⊑ Predicated` — a checkbox retains at least as much of
     the quality as nothing at all (the duck check survives: neither is thereby
     conflated with attenuation, and every floor above `Dropped` still rejects
     both).
   Under (A1)+(A2): composition is **commutative** (`FateA.comp_comm`),
   **monotone in both arguments** (`FateA.comp_mono_left/right`), the order is
   **linear** (`FateA.le_total`) — hence (with the fidelity chain complete) a
   complete chain, restoring §7's Knaster–Tarski justification — and the
   cancellation boundary of `GradeBoundary.lean` is **preserved**
   (`FateA.falsified_two_sided_zero`, `FateA.dropped_still_not_cancel`).

The shipped carrier is **not** changed by this file; `FateA` is a probe, like
`grade-factorisation`. Adopting (A1)/(A2) is an owner decision (they touch the
duck check and would *retire* `grade_mul_not_comm` — non-commutativity is an
artifact of the unamended clause, not intrinsic to loss-shape grading).
-/

namespace Trope

/-! ## The retention order on the shipped carrier (mirror of `fateLte`) -/

namespace Fate

/-- Retention order ⊑ on the shipped fate carrier, mirroring `Coords.idr`'s
`fateLte` clause-for-clause (`x ⊑ y` ⇔ `y` retains at least as much as `x`).
On `Delta = WithTop (WithTop ℕ)` the retention order is the *reverse* of the
canonical ≤ (more loss = less retention). -/
def le : Fate → Fate → Prop
  | falsified,  _          => True
  | _,          falsified  => False
  | _,          present    => True
  | present,    _          => False
  | atten a,    atten b    => b ≤ a
  | atten _,    predicated => False
  | atten _,    dropped    => False
  | predicated, atten _    => True
  | predicated, predicated => True
  | predicated, dropped    => False
  | dropped,    atten _    => True
  | dropped,    predicated => False
  | dropped,    dropped    => True

/-- **L4 fails in the right argument on the shipped carrier.** Witness: composing
`Predicated` (a collapse) after `Dropped ⊑ Atten (Q 0)` lands on the
`{Predicated, Dropped}` antichain: `Predicated ▷ Dropped = Dropped` while
`Predicated ▷ Atten (Q 0) = Predicated`, and `Dropped ⋢ Predicated`. -/
theorem comp_not_monotone_right :
    ∃ h x y : Fate, le x y ∧ ¬ le (h * x) (h * y) := by
  refine ⟨predicated, dropped, atten (Delta.Q 1), trivial, ?_⟩
  show ¬ le (comp predicated dropped) (comp predicated (atten (Delta.Q 1)))
  simp [comp, le]

/-- **L4 fails in the left argument on the shipped carrier.** Witness: with
`Dropped ⊑ Atten (Q 0)`, composing a downstream `Falsified`:
`Dropped ▷ Falsified = Dropped` (the drop *erases* the lie) while
`Atten (Q 0) ▷ Falsified = Falsified`, and `Dropped ⋢ Falsified`. -/
theorem comp_not_monotone_left :
    ∃ x y h : Fate, le x y ∧ ¬ le (x * h) (y * h) := by
  refine ⟨dropped, atten (Delta.Q 1), falsified, trivial, ?_⟩
  show ¬ le (comp dropped falsified) (comp (atten (Delta.Q 1)) falsified)
  simp [comp, le]

/-- The second left-argument failure family: `Dropped ⊑ Present` composed with a
downstream collapse lands on the antichain again. -/
theorem comp_not_monotone_left' :
    ∃ x y h : Fate, le x y ∧ ¬ le (x * h) (y * h) := by
  refine ⟨dropped, present, predicated, trivial, ?_⟩
  show ¬ le (comp dropped predicated) (comp present predicated)
  simp [comp, le]

end Fate

/-! ## The amended carrier `FateA` — two changes, three properties restored -/

namespace FateA

open Fate (present atten predicated dropped falsified)

/-- Amended composition: identical to `Fate.comp` except **(A1)**
`Dropped ▷ Falsified = Falsified` — the deceptive bottom is a two-sided zero. -/
def comp : Fate → Fate → Fate
  | falsified,  _          => falsified
  | dropped,    falsified  => falsified        -- (A1): the lie survives the drop
  | dropped,    _          => dropped
  | present,    f          => f
  | atten _,    falsified  => falsified
  | atten _,    dropped    => dropped
  | atten d,    present    => atten d
  | atten d1,   atten d2   => atten (d1 + d2)
  | atten _,    predicated => predicated
  | predicated, falsified  => falsified
  | predicated, dropped    => dropped
  | predicated, present    => predicated
  | predicated, atten _    => predicated
  | predicated, predicated => predicated

/-- Amended retention order: identical to `Fate.le` except **(A2)**
`Dropped ⊑ Predicated`. The order becomes a chain:
`Falsified ⊏ Dropped ⊏ Predicated ⊏ Atten δ ⊏ Present` (with the `Atten`
segment ordered by the fidelity chain). -/
def le : Fate → Fate → Prop
  | falsified,  _          => True
  | _,          falsified  => False
  | _,          present    => True
  | present,    _          => False
  | atten a,    atten b    => b ≤ a
  | atten _,    predicated => False
  | atten _,    dropped    => False
  | predicated, atten _    => True
  | predicated, predicated => True
  | predicated, dropped    => False
  | dropped,    atten _    => True
  | dropped,    predicated => True             -- (A2): a checkbox ⊒ nothing
  | dropped,    dropped    => True

/-- The amended order is reflexive. -/
theorem le_refl : ∀ f : Fate, le f f := by
  intro f; cases f <;> simp [le]

/-- The amended order is **total** (a chain). With the fidelity segment a
complete linear order (`ℕ ∪ {∞, ⊤}`), the amended fate carrier is a complete
chain — exactly what §7's Knaster–Tarski argument needs. -/
theorem le_total : ∀ a b : Fate, le a b ∨ le b a := by
  intro a b
  cases a <;> cases b <;> simp [le] <;> exact _root_.le_total _ _

/-- **Commutativity.** With (A1), amended composition is commutative: the sole
non-commuting pair of the shipped carrier was `(Dropped, Falsified)`. -/
theorem comp_comm : ∀ a b : Fate, comp a b = comp b a := by
  intro a b
  cases a <;> cases b <;> simp [comp]
  exact _root_.add_comm _ _

/-- Amended composition is associative (unchanged cases + the (A1) clause). -/
theorem comp_assoc : ∀ a b c : Fate, comp (comp a b) c = comp a (comp b c) := by
  intro a b c
  cases a <;> cases b <;> cases c <;> simp [comp]
  exact _root_.add_assoc _ _ _

/-- `Present` is still the unit. -/
theorem comp_one : ∀ f : Fate, comp f present = f := by
  intro f; cases f <;> rfl
theorem one_comp : ∀ f : Fate, comp present f = f := by
  intro f; rfl

/-- **L4 restored, right argument**: amended composition is monotone in its
right argument w.r.t. the amended retention order. -/
theorem comp_mono_right :
    ∀ h x y : Fate, le x y → le (comp h x) (comp h y) := by
  intro h x y hxy
  cases h <;> cases x <;> cases y <;> simp_all [comp, le] <;>
    exact add_le_add_left hxy _

/-- **L4 restored, left argument**: amended composition is monotone in its
left argument w.r.t. the amended retention order. -/
theorem comp_mono_left :
    ∀ x y h : Fate, le x y → le (comp x h) (comp y h) := by
  intro x y h hxy
  cases x <;> cases y <;> cases h <;> simp_all [comp, le] <;>
    exact add_le_add_right hxy _

/-! ### The boundary survives the repair -/

/-- (A1) makes `Falsified` a **two-sided zero**: L5 strengthened — deception is
infectious in both composition directions; no honest absorber launders it. -/
theorem falsified_two_sided_zero :
    (∀ f : Fate, comp falsified f = falsified) ∧
    (∀ f : Fate, comp f falsified = falsified) := by
  refine ⟨fun f => rfl, fun f => ?_⟩
  cases f <;> rfl

/-- `Dropped` still absorbs every *honest* right operand, so it remains
non-cancellative (tier 2 is intact under the repair). -/
theorem dropped_still_not_cancel :
    comp dropped present = comp dropped predicated ∧ (present ≠ predicated) := by
  exact ⟨rfl, by intro h; exact Fate.noConfusion h⟩

/-- Conicality survives: the unit is reachable only from units. -/
theorem conical (a b : Fate) (h : comp a b = present) : a = present ∧ b = present := by
  cases a <;> cases b <;> simp_all [comp]

end FateA

end Trope

/-! ## Axiom audit (sorry-free check) -/
section AxiomAudit
open Trope
#print axioms Trope.Fate.comp_not_monotone_right
#print axioms Trope.Fate.comp_not_monotone_left
#print axioms Trope.Fate.comp_not_monotone_left'
#print axioms Trope.FateA.le_total
#print axioms Trope.FateA.comp_comm
#print axioms Trope.FateA.comp_assoc
#print axioms Trope.FateA.comp_mono_right
#print axioms Trope.FateA.comp_mono_left
#print axioms Trope.FateA.falsified_two_sided_zero
#print axioms Trope.FateA.dropped_still_not_cancel
#print axioms Trope.FateA.conical
end AxiomAudit
