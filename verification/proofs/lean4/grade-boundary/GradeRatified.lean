-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
import L4Monotonicity
import TierTwoComplete

/-!
# The RATIFIED grade algebra (R-2026-07-07, ADR 0004) — full mirror + ported boundary

`GradeBoundary.lean` mirrors the *pre-ratification* carrier (kept, under its
provenance note, for the historical record). This file is the mirror of the
**ratified** carrier (issue #29, task 1): the grade record over the ratified
fate coordinate — which is exactly `Trope.FateA` of `L4Monotonicity.lean`
(amendments (A1) `Dropped ▷ Falsified = Falsified` and (A2)
`Dropped ⊑ Predicated`, ratified in ADR 0004 as R-2026-07-07-01 and -02) — with the
`Bond` and `Merge` coordinates unchanged from `GradeBoundary.lean`.

## What is proved (sorry-free; `#print axioms` at the foot)

* **`CommMonoid GradeR`** (`instCommMonoid`) — the ratified grade algebra is a
  *commutative* monoid, componentwise. This formally retires
  `GradeBoundary.grade_mul_not_comm` for the ratified carrier:
  non-commutativity was an artifact of the unamended
  `Dropped ▷ Falsified = Dropped` clause, exactly as ADR 0004 records.
* **Conicality** (`conical`) — unchanged in kind: `a ▷ b = ε ⇒ a = ε ∧ b = ε`.
* **Deceptive bottoms are still two-sided zeros** (`gBotR_two_sided_zero`,
  with the coordinate-level `Bond.mul_misbound` / `Merge.mul_conflated`
  supplements and `FateA.falsified_two_sided_zero` from `L4Monotonicity.lean`):
  (A1) strengthened L5 to both sides, so this is now a *theorem of the
  carrier*, not of one composition order.
* **`Dropped` is still non-cancellative** (`gDroppedR_not_cancel`,
  `gradeR_not_leftCancel`) — `FateA.dropped_still_not_cancel` lifts to the
  grade level: the honest-withholding absorber keeps tier 2 inhabited.
* **The cancellation classification survives, carrier-level**
  (`gradeR_leftCancel_iff`): an element of the *unquotiented* ratified grade
  monoid is left-cancellative iff it is the unit ε — same statement as
  `TierTwoComplete.grade_leftCancel_iff`, now over the ratified composition.
* **The A3 refinement** (`FateA.atten_cancel_on_normalForms`): under ADR 0004's
  R-2026-07-07-03, `Attenuated(Q 0)` is normalized to `Present` at IR ingest,
  so stored/composed grades never contain `atten (Q 0)`. Among such **normal
  forms** the carrier-level collision witness (`present` vs `atten (Q 0)`)
  disappears and finite attenuation **is** left-cancellative on the fate
  coordinate: `atten (Q n) ▷ x = atten (Q n) ▷ y → x = y` whenever
  `x, y ≠ atten (Q 0)`. So the classification is A3-sensitive exactly as issue
  #29 anticipated: unquotiented tier 1 = `{ε}`; under A3 normal forms, finite
  attenuation rejoins tier 1 on the fate axis.
-/

namespace Trope

/-! ## Supplementary coordinate lemmas

`Bond`/`Merge` are unchanged by ratification, but ADR 0004 (A1) states the
deceptive bottoms are *two-sided* zeros; `GradeBoundary.lean` only records the
left form (`misbound_absorbing`, `conflated_absorbing`). The right forms follow
from commutativity — recorded here so the grade-level two-sided-zero theorem
can cite them directly. -/

namespace Bond

/-- `Misbound` absorbs on the right too (it always did — `Bond` is commutative). -/
@[simp] theorem mul_misbound (b : Bond) : b * misbound = misbound := by
  cases b <;> rfl

end Bond

namespace Merge

/-- `Conflated` absorbs on the right too (it always did — `Merge` is commutative). -/
@[simp] theorem mul_conflated (m : Merge) : m * conflated = conflated := by
  cases m <;> rfl

end Merge

/-! ## Ratified-fate supplements: cancellation structure of `FateA.comp` -/

namespace FateA

open Fate (present atten predicated dropped falsified)

/-- **Every non-unit ratified fate fails left-cancellation** (carrier-level,
i.e. *unquotiented*: `atten (Q 0)` is a legal operand). The `atten` witness is
the `present`/`atten (Q 0)` collision — exactly the witness that A3
normalization removes (see `atten_cancel_on_normalForms`). All other witnesses
are A3-robust. -/
theorem leftCancelWitness :
    ∀ f : Fate, f ≠ present → ∃ x y : Fate, comp f x = comp f y ∧ x ≠ y := by
  intro f hf
  cases f with
  | present => exact absurd rfl hf
  | atten d =>
      refine ⟨present, atten (Delta.Q 0), ?_, by intro h; exact Fate.noConfusion h⟩
      simp [comp, Delta.Q_zero]
  | predicated =>
      exact ⟨present, predicated, rfl, by intro h; exact Fate.noConfusion h⟩
  | dropped =>
      exact ⟨present, predicated, rfl, by intro h; exact Fate.noConfusion h⟩
  | falsified =>
      exact ⟨present, predicated, rfl, by intro h; exact Fate.noConfusion h⟩

/-- The unit is left-cancellative (trivially). -/
theorem present_leftCancel : ∀ x y : Fate, comp present x = comp present y → x = y := by
  intro x y h; simpa [comp] using h

/-! ### The A3 refinement: finite attenuation cancels among normal forms

ADR 0004 R-2026-07-07-03: validators rewrite `Attenuated(Q 0)` to `Present` at
IR ingest, and composition preserves normal forms (finite tropical addition
reaches 0 only from 0 + 0). So the operands that actually occur in stored or
composed grades never include `atten (Q 0)`, and on that restricted domain the
sole collision behind `leftCancelWitness`'s `atten` case is gone. -/

/-- Left-cancellation of a fixed finite coefficient inside the fidelity
carrier: `Q n + d = Q n + e → d = e`. (Note this is *stronger* than ℕ-core
cancellation: it holds for **all** `d e : Delta`, absorbing tops included,
because `Q n + ⊤' `-style sums are distinguishable by which top they hit.) -/
theorem Q_add_left_cancel {n : ℕ} {d e : Delta} (h : Delta.Q n + d = Delta.Q n + e) :
    d = e := by
  unfold Delta.Q at h
  induction d using WithTop.recTopCoe with
  | top =>
    induction e using WithTop.recTopCoe with
    | top => rfl
    | coe e' =>
      rw [add_top, ← WithTop.coe_add] at h
      exact absurd h.symm (WithTop.coe_ne_top)
  | coe d' =>
    induction e using WithTop.recTopCoe with
    | top =>
      rw [add_top, ← WithTop.coe_add] at h
      exact absurd h (WithTop.coe_ne_top)
    | coe e' =>
      rw [← WithTop.coe_add, ← WithTop.coe_add] at h
      have h' : (n : WithTop ℕ) + d' = (n : WithTop ℕ) + e' := WithTop.coe_injective h
      have hde : d' = e' := WithTop.add_left_cancel WithTop.coe_ne_top h'
      rw [hde]

/-- **Finite attenuation is left-cancellative among A3 normal forms.** For any
finite coefficient `Q n` and any right operands that are normal forms (exclude
`atten (Q 0)`), `atten (Q n) ▷ x = atten (Q n) ▷ y → x = y`. Under ADR 0004
(A3) this is the operative statement: finite attenuation rejoins tier 1 on the
fate coordinate. (Carrier-level, without the normal-form hypotheses, it is
*false* — `leftCancelWitness` exhibits the `present`/`atten (Q 0)` collision.) -/
theorem atten_cancel_on_normalForms (n : ℕ) (x y : Fate)
    (hx : x ≠ atten (Delta.Q 0)) (hy : y ≠ atten (Delta.Q 0))
    (h : comp (atten (Delta.Q n)) x = comp (atten (Delta.Q n)) y) : x = y := by
  cases x <;> cases y <;> simp_all [comp]
  case atten.atten dx dy => exact Q_add_left_cancel h
  case present.atten dy =>
    -- `atten (Q n) = atten (Q n + dy)` forces `dy = Q 0`, excluded by `hy`
    exfalso
    have h0 : Delta.Q n + 0 = Delta.Q n + dy := by simpa using h
    have : (0 : Delta) = dy := Q_add_left_cancel h0
    exact hy (by simp [← this, Delta.Q_zero])
  case atten.present dx =>
    exfalso
    have h0 : Delta.Q n + dx = Delta.Q n + 0 := by simpa using h
    have : dx = (0 : Delta) := Q_add_left_cancel h0
    exact hx (by simp [this, Delta.Q_zero])

end FateA

/-! ## The ratified grade `GradeR`: the flat record over the ratified fate -/

/-- The ratified grade record: same shape as `Grade` (`Grade.idr` §3), but its
fate coordinates compose by the **ratified** `FateA.comp`. Kept as a separate
structure so both mirrors coexist and the historical theorems keep their
subjects. -/
structure GradeR where
  fQuality : Fate
  fBearer  : Fate
  fContext : Fate
  fRecord  : Fate
  bond     : Bond
  merge    : Merge
deriving DecidableEq

namespace GradeR

/-- The unit grade ε: full presence everywhere, intact, single. -/
def epsilonR : GradeR :=
  ⟨Fate.present, Fate.present, Fate.present, Fate.present, Bond.intact, Merge.single⟩

/-- Ratified composition ▷, componentwise: `FateA.comp` on the four fate slots,
the (unchanged) coordinate `*` on bond and merge. -/
def gcomp (g h : GradeR) : GradeR where
  fQuality := FateA.comp g.fQuality h.fQuality
  fBearer  := FateA.comp g.fBearer  h.fBearer
  fContext := FateA.comp g.fContext h.fContext
  fRecord  := FateA.comp g.fRecord  h.fRecord
  bond     := g.bond  * h.bond
  merge    := g.merge * h.merge

instance : Mul GradeR := ⟨gcomp⟩
instance : One GradeR := ⟨epsilonR⟩

theorem mul_def (g h : GradeR) : g * h = gcomp g h := rfl
@[simp] theorem one_def : (1 : GradeR) = epsilonR := rfl

/-- **The ratified grade algebra is a commutative monoid.** Componentwise:
associativity/unit/commutativity of the fate slots from
`FateA.comp_assoc`/`comp_one`/`one_comp`/`comp_comm` (`L4Monotonicity.lean`),
bond/merge from their (unchanged) `CommMonoid` instances. The existence of this
instance *is* the retirement of `grade_mul_not_comm` for the ratified carrier:
the ratified ▷ is commutative, so the stronger `CommMonoid` now models it. -/
instance instCommMonoid : CommMonoid GradeR where
  mul := gcomp
  one := epsilonR
  mul_assoc a b c := by
    cases a; cases b; cases c
    simp only [mul_def, gcomp, FateA.comp_assoc, mul_assoc]
  one_mul a := by
    cases a
    simp only [mul_def, gcomp, one_def, epsilonR,
      FateA.one_comp, Bond.intact_mul, Merge.single_mul]
  mul_one a := by
    cases a
    simp only [mul_def, gcomp, one_def, epsilonR,
      FateA.comp_one, Bond.mul_intact, Merge.mul_single]
  mul_comm a b := by
    cases a; cases b
    simp only [mul_def, gcomp, FateA.comp_comm, mul_comm]

/-! ### Conicality (ported) -/

/-- `a ▷ b = ε ⇒ a = ε ∧ b = ε`: the ratified carrier is conical (the unit is
reachable only from units). Coordinate conicality: `FateA.conical`,
`Bond.conical`, `Merge.conical`. -/
theorem conical (a b : GradeR) (h : a * b = 1) : a = 1 ∧ b = 1 := by
  cases a; cases b
  simp only [mul_def, gcomp, one_def, epsilonR, GradeR.mk.injEq] at h
  obtain ⟨hq, hbr, hc, hr, hbo, hm⟩ := h
  obtain ⟨haq, hbq⟩ := FateA.conical _ _ hq
  obtain ⟨habr, hbbr⟩ := FateA.conical _ _ hbr
  obtain ⟨hac, hbc⟩ := FateA.conical _ _ hc
  obtain ⟨har, hbr'⟩ := FateA.conical _ _ hr
  obtain ⟨habo, hbbo⟩ := Bond.conical _ _ hbo
  obtain ⟨ham, hbm⟩ := Merge.conical _ _ hm
  constructor
  · simp only [one_def, epsilonR, GradeR.mk.injEq]
    exact ⟨haq, habr, hac, har, habo, ham⟩
  · simp only [one_def, epsilonR, GradeR.mk.injEq]
    exact ⟨hbq, hbbr, hbc, hbr', hbbo, hbm⟩

/-! ### Deceptive bottoms: still two-sided zeros (ported, and now two-sided by A1) -/

/-- The all-deceptive bottom grade: `Falsified` in every fate slot, `Misbound`,
`Conflated`. -/
def gBotR : GradeR :=
  ⟨Fate.falsified, Fate.falsified, Fate.falsified, Fate.falsified,
   Bond.misbound, Merge.conflated⟩

/-- **The deceptive bottom is a two-sided zero of the ratified grade monoid.**
Pre-ratification this held only on the left (the `Dropped ▷ Falsified =
Dropped` clause let an upstream drop launder a downstream lie); (A1) closed
that hole, so L5 now holds in both composition orders — deception is
infectious, full stop. -/
theorem gBotR_two_sided_zero (g : GradeR) : gBotR * g = gBotR ∧ g * gBotR = gBotR := by
  obtain ⟨hl, hr⟩ := FateA.falsified_two_sided_zero
  cases g
  constructor
  · show gcomp _ _ = _
    simp only [gcomp, gBotR, hl, Bond.misbound_absorbing, Merge.conflated_absorbing]
  · show gcomp _ _ = _
    simp only [gcomp, gBotR, hr, Bond.mul_misbound, Merge.mul_conflated]

/-! ### `Dropped` still non-cancellative (ported) -/

/-- The honest-withholding grade (unit everywhere except `fQuality = dropped`). -/
def gDroppedR : GradeR :=
  ⟨Fate.dropped, Fate.present, Fate.present, Fate.present, Bond.intact, Merge.single⟩

/-- The deceptive grade (unit everywhere except `fQuality = falsified`). -/
def gFalsifiedR : GradeR :=
  ⟨Fate.falsified, Fate.present, Fate.present, Fate.present, Bond.intact, Merge.single⟩

/-- `FateA.dropped_still_not_cancel` lifted to the grade level: `gDroppedR`
absorbs the difference between the unit grade and the predicated grade, so
`Dropped` remains non-cancellative under ratification (tier 2 stays inhabited). -/
theorem gDroppedR_not_cancel :
    gDroppedR * (1 : GradeR) =
      gDroppedR * ⟨Fate.predicated, .present, .present, .present, .intact, .single⟩ ∧
    (1 : GradeR) ≠ (⟨Fate.predicated, .present, .present, .present, .intact, .single⟩ : GradeR) := by
  exact ⟨by decide, by decide⟩

/-- Hence the ratified grade monoid is **not** left-cancellative (commutativity
gained cancellativity nothing — the absorbing structure, not the ordering of
the two absorbing heads, is what blocks it). -/
theorem gradeR_not_leftCancel : ∃ a x y : GradeR, a * x = a * y ∧ x ≠ y :=
  ⟨gDroppedR, _, _, gDroppedR_not_cancel⟩

/-! ### The cancellation classification (ported, carrier-level)

**A3 caveat (ADR 0004 R-2026-07-07-03).** The classification below is about the
carrier **as-is** (unquotiented): `atten (Q 0)` is a legal value and collides
with `present` under any `atten`-headed left factor, which is what pins tier 1
to `{ε}`. Under A3, `Attenuated(Q 0)` is normalized to `Present` at IR ingest
and composition preserves normal forms, so that witness never occurs among
stored/composed grades — and among normal forms finite attenuation IS
left-cancellative on the fate coordinate (`FateA.atten_cancel_on_normalForms`:
`atten (Q n) ▷ present = atten (Q n)` vs `atten (Q n) ▷ atten (Q m) =
atten (Q (n+m))` with `m ≥ 1` never collide). So under A3 normal forms, tier 1
at the fate level is the finite-attenuation core + unit, recovering
`GradeBoundary.lean`'s original "finite-fidelity + units" reading; the `{ε}`
classification below is the unquotiented-carrier statement only. -/

private theorem lift_fQuality (g : GradeR)
    (hw : ∃ x y : Fate, FateA.comp g.fQuality x = FateA.comp g.fQuality y ∧ x ≠ y) :
    ∃ x y : GradeR, g * x = g * y ∧ x ≠ y := by
  obtain ⟨xf, yf, hxy, hne⟩ := hw
  refine ⟨⟨xf, .present, .present, .present, .intact, .single⟩,
          ⟨yf, .present, .present, .present, .intact, .single⟩, ?_, ?_⟩
  · show gcomp g _ = gcomp g _
    simp [gcomp, hxy]
  · intro h
    exact hne (congrArg GradeR.fQuality h)

private theorem lift_fBearer (g : GradeR)
    (hw : ∃ x y : Fate, FateA.comp g.fBearer x = FateA.comp g.fBearer y ∧ x ≠ y) :
    ∃ x y : GradeR, g * x = g * y ∧ x ≠ y := by
  obtain ⟨xf, yf, hxy, hne⟩ := hw
  refine ⟨⟨.present, xf, .present, .present, .intact, .single⟩,
          ⟨.present, yf, .present, .present, .intact, .single⟩, ?_, ?_⟩
  · show gcomp g _ = gcomp g _
    simp [gcomp, hxy]
  · intro h
    exact hne (congrArg GradeR.fBearer h)

private theorem lift_fContext (g : GradeR)
    (hw : ∃ x y : Fate, FateA.comp g.fContext x = FateA.comp g.fContext y ∧ x ≠ y) :
    ∃ x y : GradeR, g * x = g * y ∧ x ≠ y := by
  obtain ⟨xf, yf, hxy, hne⟩ := hw
  refine ⟨⟨.present, .present, xf, .present, .intact, .single⟩,
          ⟨.present, .present, yf, .present, .intact, .single⟩, ?_, ?_⟩
  · show gcomp g _ = gcomp g _
    simp [gcomp, hxy]
  · intro h
    exact hne (congrArg GradeR.fContext h)

private theorem lift_fRecord (g : GradeR)
    (hw : ∃ x y : Fate, FateA.comp g.fRecord x = FateA.comp g.fRecord y ∧ x ≠ y) :
    ∃ x y : GradeR, g * x = g * y ∧ x ≠ y := by
  obtain ⟨xf, yf, hxy, hne⟩ := hw
  refine ⟨⟨.present, .present, .present, xf, .intact, .single⟩,
          ⟨.present, .present, .present, yf, .intact, .single⟩, ?_, ?_⟩
  · show gcomp g _ = gcomp g _
    simp [gcomp, hxy]
  · intro h
    exact hne (congrArg GradeR.fRecord h)

private theorem lift_bond (g : GradeR)
    (hw : ∃ x y : Bond, g.bond * x = g.bond * y ∧ x ≠ y) :
    ∃ x y : GradeR, g * x = g * y ∧ x ≠ y := by
  obtain ⟨xb, yb, hxy, hne⟩ := hw
  refine ⟨⟨.present, .present, .present, .present, xb, .single⟩,
          ⟨.present, .present, .present, .present, yb, .single⟩, ?_, ?_⟩
  · show gcomp g _ = gcomp g _
    simp [gcomp, hxy]
  · intro h
    exact hne (congrArg GradeR.bond h)

private theorem lift_merge (g : GradeR)
    (hw : ∃ x y : Merge, g.merge * x = g.merge * y ∧ x ≠ y) :
    ∃ x y : GradeR, g * x = g * y ∧ x ≠ y := by
  obtain ⟨xm, ym, hxy, hne⟩ := hw
  refine ⟨⟨.present, .present, .present, .present, .intact, xm⟩,
          ⟨.present, .present, .present, .present, .intact, ym⟩, ?_, ?_⟩
  · show gcomp g _ = gcomp g _
    simp [gcomp, hxy]
  · intro h
    exact hne (congrArg GradeR.merge h)

/-- **The cancellation classification, ratified carrier, unquotiented.** An
element of the ratified grade monoid as-implemented is left-cancellative
**iff** it is the unit ε. (See the A3 caveat in the section docstring: among A3
normal forms the fate-axis `atten` case regains cancellativity, via
`FateA.atten_cancel_on_normalForms`.) -/
theorem gradeR_leftCancel_iff (g : GradeR) :
    (∀ x y : GradeR, g * x = g * y → x = y) ↔ g = 1 := by
  constructor
  · intro hc
    by_contra hne
    have : ∃ x y : GradeR, g * x = g * y ∧ x ≠ y := by
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
                  simp [one_def, epsilonR, hq, hbr, hcx, hr, hbo, hm]
                · exact lift_merge g (Merge.leftCancelWitness _ hm)
              · exact lift_bond g (Bond.leftCancelWitness _ hbo)
            · exact lift_fRecord g (FateA.leftCancelWitness _ hr)
          · exact lift_fContext g (FateA.leftCancelWitness _ hcx)
        · exact lift_fBearer g (FateA.leftCancelWitness _ hbr)
      · exact lift_fQuality g (FateA.leftCancelWitness _ hq)
    obtain ⟨x, y, hxy, hne'⟩ := this
    exact hne' (hc x y hxy)
  · rintro rfl
    intro x y h
    cases x; cases y
    simpa [mul_def, gcomp, one_def, epsilonR, FateA.one_comp,
           GradeR.mk.injEq] using h

end GradeR

end Trope

/-! ## Axiom audit (sorry-free check) -/
section AxiomAudit
open Trope
#print axioms Trope.GradeR.instCommMonoid
#print axioms Trope.GradeR.conical
#print axioms Trope.GradeR.gBotR_two_sided_zero
#print axioms Trope.GradeR.gDroppedR_not_cancel
#print axioms Trope.GradeR.gradeR_not_leftCancel
#print axioms Trope.GradeR.gradeR_leftCancel_iff
#print axioms Trope.FateA.leftCancelWitness
#print axioms Trope.FateA.Q_add_left_cancel
#print axioms Trope.FateA.atten_cancel_on_normalForms
#print axioms Trope.Bond.mul_misbound
#print axioms Trope.Merge.mul_conflated
end AxiomAudit
