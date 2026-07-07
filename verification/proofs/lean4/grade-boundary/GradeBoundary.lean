-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
import Mathlib

/-!
# The trope-particularity grade algebra — the honest/deceptive cancellation boundary

Calculus spec `spec/calculus.adoc`, `:revnumber: 0.1`. Ground-truth carrier:
`verification/proofs/idris2/Trope/{Fidelity,Coords,Grade}.idr`.

> **Provenance note (R-2026-07-07, ADR 0004).** This file mirrors the
> *pre-ratification* carrier. The ratified carrier adopts (A1)
> `Dropped ▷ Falsified = Falsified` and (A2) `Dropped ⊑ Predicated`
> (see `L4Monotonicity.lean`, whose `FateA` namespace *is* the ratified fate
> coordinate). In particular `grade_mul_not_comm` below is a theorem about the
> pre-ratification carrier only — non-commutativity was an artifact of the
> unamended clause, and the ratified algebra is commutative. The cancellation
> boundary results carry over in kind (see `FateA.dropped_still_not_cancel`).
> A full re-mirror of the ratified carrier is tracked as a follow-up.

## Provenance and scope (read first)

* There is **no v0.2** of the spec. In v0.1, "O1" = "completeness of the seven
  effects"; that O1 is out of scope and untouched here.
* **No Frobenius / cancellative / conical framing exists in the spec.** Grep of
  `spec/calculus.adoc` finds none (the only hit is O3, the produce/demand
  *adjunction* open question, which is unrelated). This file is therefore **new
  work**, not a transcription of spec text.
* "CF" (coordinate-factorisation: cancellative + conical ⇒ lossless special-
  Frobenius split/merge) was a *proposed* structure. **CF-as-universal is refuted
  by L5**: every composition is a meet with an absorbing *deceptive bottom*, so the
  carrier is **non-cancellative by design** — deception must be irreversible
  (cancellation would let deception be "subtracted back out", i.e. forged away).
  The target here is therefore not "prove CF" but to **characterise the boundary**:
  cancellation fails on the absorbing elements and holds on the honest finite-
  fidelity core.

## What is proved (sorry-free; see `#print axioms` block at the foot)

* **Deliverable 1 (Discriminator).** `instance : Monoid Grade` as the componentwise
  product of the coordinate monoids — DEGENERATE-TO-PRODUCT confirmed
  constructively. Refinement discovered against the carrier: the product is
  **non-commutative** (`grade_mul_not_comm`), because `Fate` has *two* distinct
  left-absorbing heads (`dropped`, `falsified`) that disagree on order. Hence the
  stronger `CommMonoid`/`AddCommMonoid` does **not** model `▷`. This sharpens, but
  does not overturn, the verdict.
* **Deliverable 2 (Conicality, full carrier).** `grade_conical : a * b = 1 → a = 1 ∧ b = 1`.
* **Deliverable 3 (Cancellation boundary).**
  - Deceptive bottoms are left zeros (absorbing) — `*_absorbing` — hence the full
    carrier is non-left-cancellative (`grade_not_leftCancel`). This is L5.
  - The honest finite-fidelity region is a cancellative submonoid: `Delta.Q` is an
    injective additive monoid hom of `(ℕ,+,0)` and cancels (`honest_fidelity_cancel`).
  - The boundary is **sharper than a two-tier honest/deceptive split**: honest-but-
    lossy elements (`severed`, `dropped`, `predicated`, `total`) are *also* non-
    cancellative (`*_honest_not_cancel`). So the non-cancellative set strictly
    contains the deceptive set; the cancellative core is exactly the finite-fidelity
    additive part (+ units).

## Discrepancy with the task's stated partition (using the SOURCE, as instructed)

The task brief listed the deceptive (absorbing) set as
`{Dropped, Falsified, Misbound, Conflated, Unknown, Total}`. The **carrier**
(`Coords.idr` doc-comment + the order `fateLte`) says each coordinate has exactly
**one** deceptive inhabitant = its unique order-bottom: `Falsified` (fate),
`Misbound` (bond), `Conflated` (merge); `Unknown` is fidelity's absorbing bottom.
`Dropped` is *honest withholding* ("withheld entirely"; its deceptive dual is
`Falsified`) and is incomparable to `Predicated`, sitting strictly above the
`Falsified` bottom. `Total` is the *honest* "∞ total loss" (`Fidelity.idr` line 4),
absorbing over finite δ but not a lie. So `Dropped` and `Total` are honest-but-
absorbing, **not** deceptive. This file uses the source classification — and the
discrepancy is exactly *why* "cancellation fails ⇔ deceptive" is false: `Dropped`,
`Total`, `severed`, `predicated` are non-deceptive yet non-cancellative.
-/

namespace Trope

/-! ## Fidelity coordinate `Delta = WithTop (WithTop ℕ)`

`Fidelity.idr`: `Delta = Q ℕ | Total | Unknown`, tropical (min-plus) addition with
`Unknown` absorbing `Total` absorbing finite, unit `Q 0`. Structurally this is
`WithTop (WithTop ℕ)`: `Q n ↔ ↑↑n`, `Total ↔ ↑⊤` (inner top), `Unknown ↔ ⊤` (outer
top); `dplus = (+)`; `Q 0 = 0`. We take the Mathlib monoid wholesale, so
associativity, unit, and absorption come from `WithTop`. -/

abbrev Delta := WithTop (WithTop ℕ)

namespace Delta

/-- Finite quantified loss `Q n` (the honest, non-absorbing region). -/
def Q (n : ℕ) : Delta := ((n : WithTop ℕ) : Delta)
/-- `Total` (∞): honest total loss; the inner top. Absorbs finite, absorbed by `Unknown`. -/
def total : Delta := ((⊤ : WithTop ℕ) : Delta)
/-- `Unknown` (⊤): loss of unknown amount; the absorbing bottom of fidelity (L5). -/
def unknown : Delta := (⊤ : Delta)

/-- `dplus`'s finite clause: `Q a ▷ Q c = Q (a+c)` — the tropical add of `Fidelity.idr`. -/
@[simp] theorem Q_add (a c : ℕ) : Q a + Q c = Q (a + c) := by unfold Q; norm_cast

/-- The unit grade's fidelity: `Q 0 = 0`. -/
@[simp] theorem Q_zero : Q 0 = 0 := by unfold Q; norm_cast

/-- `Q` is injective: distinct finite losses are distinct grades. -/
theorem Q_injective : Function.Injective Q := by
  intro a b h; unfold Q at h; exact_mod_cast h

/-- `Unknown` is a left zero (absorbing) — L5: unknown loss cannot be recovered. -/
@[simp] theorem unknown_absorbing (d : Delta) : unknown + d = unknown := by
  unfold unknown; exact top_add d

/-- `Total` absorbs finite loss (`dplus Total (Q n) = Total`). -/
theorem total_add_Q (n : ℕ) : total + Q n = total := by unfold total Q; rfl

/-- …but `Unknown` absorbs `Total`: the absorption order is `Unknown ⊐ Total ⊐ finite`. -/
theorem total_add_unknown : total + unknown = unknown := by
  unfold total unknown; exact add_top _

end Delta

/-! ## Coordinate 1: field fate (`Coords.idr` §3.1)

A non-commutative monoid: `Present` is the unit; `Falsified` and `Dropped` are
*both* left-absorbing but disagree (`Dropped ▷ Falsified = Dropped` while
`Falsified ▷ Dropped = Falsified`), which is the source of non-commutativity. -/

inductive Fate
  | present
  | atten (d : Delta)
  | predicated
  | dropped
  | falsified
deriving DecidableEq

namespace Fate

/-- `fateCompose` of `Coords.idr`, clause-for-clause (first-match, as Idris). -/
def comp : Fate → Fate → Fate
  | falsified,  _          => falsified
  | dropped,    _          => dropped
  | present,    f          => f
  | atten _,    falsified  => falsified
  | atten _,    dropped    => dropped
  | atten d,    present     => atten d
  | atten d1,   atten d2    => atten (d1 + d2)
  | atten _,    predicated  => predicated
  | predicated, falsified   => falsified
  | predicated, dropped     => dropped
  | predicated, present     => predicated
  | predicated, atten _     => predicated
  | predicated, predicated  => predicated

instance : Mul Fate := ⟨comp⟩
instance : One Fate := ⟨present⟩

@[simp] theorem one_def : (1 : Fate) = present := rfl
theorem mul_def (a b : Fate) : a * b = comp a b := rfl

theorem one_mul' (f : Fate) : (1 : Fate) * f = f := rfl
theorem mul_one' (f : Fate) : f * (1 : Fate) = f := by cases f <;> rfl

/-- Constructor-form unit lemmas (the unit token `present`, not `1`), so the product
`Grade` instance can discharge its unit laws fieldwise by `simp`. -/
@[simp] theorem present_mul (f : Fate) : present * f = f := rfl
@[simp] theorem mul_present (f : Fate) : f * present = f := by cases f <;> rfl

theorem mul_assoc' (a b c : Fate) : a * b * c = a * (b * c) := by
  cases a <;> cases b <;> cases c <;>
    first
      | rfl
      | exact congrArg atten (add_assoc _ _ _)

instance : Monoid Fate where
  mul := comp
  one := present
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'

/-- L5 for fate: the deceptive bottom `Falsified` is a left zero (absorbing). A lie
composed with anything is the same lie — it cannot be cancelled back out. -/
@[simp] theorem falsified_absorbing (f : Fate) : falsified * f = falsified := rfl

/-- `Dropped` is *also* left-absorbing — but it is honest withholding, not deception. -/
@[simp] theorem dropped_absorbing (f : Fate) : dropped * f = dropped := rfl

/-- Conicality: the only way to compose to the unit is unit ▷ unit. -/
theorem conical (a b : Fate) (h : a * b = 1) : a = 1 ∧ b = 1 := by
  cases a <;> cases b <;> simp_all [mul_def, comp]

/-- Non-commutativity, witnessed at the two disagreeing absorbing heads. -/
theorem not_comm : ∃ a b : Fate, a * b ≠ b * a :=
  ⟨dropped, falsified, by decide⟩

/-- Left-cancellation fails at the deceptive bottom (L5, the design-critical case). -/
theorem falsified_not_cancel :
    falsified * present = falsified * dropped ∧ (present ≠ dropped) :=
  ⟨rfl, by decide⟩

/-- Left-cancellation fails at `Predicated` too — it collapses the honest part
(`present` and `atten (Q 0)` are distinct but both map to `predicated`). Honest, yet
non-cancellative: evidence the boundary is sharper than honest/deceptive. -/
theorem predicated_honest_not_cancel :
    predicated * present = predicated * atten (Delta.Q 0)
      ∧ (present ≠ atten (Delta.Q 0)) := by
  refine ⟨rfl, ?_⟩
  intro h; exact Fate.noConfusion h

end Fate

/-! ## Coordinate 2: bond (`Coords.idr`) — a commutative meet on the chain
`Intact ⊐ Withheld ⊐ Severed` with the deceptive `Misbound` absorbing. -/

inductive Bond | intact | withheld | severed | misbound
deriving DecidableEq

namespace Bond

def comp : Bond → Bond → Bond
  | intact,   intact   => intact   | intact,   withheld => withheld
  | intact,   severed  => severed  | intact,   misbound => misbound
  | withheld, intact   => withheld | withheld, withheld => withheld
  | withheld, severed  => severed  | withheld, misbound => misbound
  | severed,  intact   => severed  | severed,  withheld => severed
  | severed,  severed  => severed  | severed,  misbound => misbound
  | misbound, _        => misbound

instance : Mul Bond := ⟨comp⟩
instance : One Bond := ⟨intact⟩

theorem mul_def (a b : Bond) : a * b = comp a b := rfl

instance : CommMonoid Bond where
  mul := comp
  one := intact
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  mul_comm a b := by cases a <;> cases b <;> rfl

@[simp] theorem intact_mul (b : Bond) : intact * b = b := by cases b <;> rfl
@[simp] theorem mul_intact (b : Bond) : b * intact = b := by cases b <;> rfl

/-- L5 for bond: the deceptive bottom `Misbound` is absorbing. -/
@[simp] theorem misbound_absorbing (b : Bond) : misbound * b = misbound := rfl

theorem conical (a b : Bond) (h : a * b = 1) : a = 1 ∧ b = 1 := by
  cases a <;> cases b <;> simp_all [mul_def, comp]

/-- Honest-but-non-cancellative: `Severed` (an honest meet element, not deceptive)
absorbs everything below `Intact` on the chain. -/
theorem severed_honest_not_cancel :
    severed * intact = severed * withheld ∧ (intact ≠ withheld) :=
  ⟨rfl, by decide⟩

end Bond

/-! ## Coordinate 3: merge (`Coords.idr`) — commutative meet on `Single ⊐ Fused`
with the deceptive `Conflated` absorbing. -/

inductive Merge | single | fused | conflated
deriving DecidableEq

namespace Merge

def comp : Merge → Merge → Merge
  | single,    single    => single    | single,    fused     => fused
  | single,    conflated => conflated | fused,     single    => fused
  | fused,     fused     => fused      | fused,     conflated => conflated
  | conflated, _         => conflated

instance : Mul Merge := ⟨comp⟩
instance : One Merge := ⟨single⟩

theorem mul_def (a b : Merge) : a * b = comp a b := rfl

instance : CommMonoid Merge where
  mul := comp
  one := single
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  mul_comm a b := by cases a <;> cases b <;> rfl

@[simp] theorem single_mul (m : Merge) : single * m = m := by cases m <;> rfl
@[simp] theorem mul_single (m : Merge) : m * single = m := by cases m <;> rfl

/-- L5 for merge: the deceptive bottom `Conflated` is absorbing. -/
@[simp] theorem conflated_absorbing (m : Merge) : conflated * m = conflated := rfl

theorem conical (a b : Merge) (h : a * b = 1) : a = 1 ∧ b = 1 := by
  cases a <;> cases b <;> simp_all [mul_def, comp]

end Merge

/-! ## The grade (`Grade.idr` §3): the flat record `Fate⁴ × Bond × Merge`, fully
independent fields. -/

structure Grade where
  fQuality : Fate
  fBearer  : Fate
  fContext : Fate
  fRecord  : Fate
  bond     : Bond
  merge    : Merge
deriving DecidableEq

namespace Grade

/-- The unit grade ε (`Grade.idr` §3.4): full presence everywhere, intact, single. -/
def epsilon : Grade :=
  ⟨Fate.present, Fate.present, Fate.present, Fate.present, Bond.intact, Merge.single⟩

/-- Composition ▷, componentwise (`Grade.idr` §4), in terms of the coordinate `*`. -/
def gcomp (g h : Grade) : Grade where
  fQuality := g.fQuality * h.fQuality
  fBearer  := g.fBearer  * h.fBearer
  fContext := g.fContext * h.fContext
  fRecord  := g.fRecord  * h.fRecord
  bond     := g.bond     * h.bond
  merge    := g.merge    * h.merge

instance : Mul Grade := ⟨gcomp⟩
instance : One Grade := ⟨epsilon⟩

theorem mul_def (g h : Grade) : g * h = gcomp g h := rfl
@[simp] theorem one_def : (1 : Grade) = epsilon := rfl

/-! ### Deliverable 1 — Discriminator: DEGENERATE-TO-PRODUCT (constructive) -/

/-- Grade is the componentwise product of the coordinate monoids: a `Monoid`. The
verdict DEGENERATE-TO-PRODUCT is reconfirmed by this instance type-checking with all
laws discharged from the per-coordinate laws. -/
instance instMonoid : Monoid Grade where
  mul := gcomp
  one := epsilon
  mul_assoc a b c := by
    cases a; cases b; cases c
    simp only [mul_def, gcomp, mul_assoc]
  one_mul a := by
    cases a
    simp only [mul_def, gcomp, one_def, epsilon,
      Fate.present_mul, Bond.intact_mul, Merge.single_mul]
  mul_one a := by
    cases a
    simp only [mul_def, gcomp, one_def, epsilon,
      Fate.mul_present, Bond.mul_intact, Merge.mul_single]

/-- Refinement of the verdict against the carrier: the product is **not commutative**
(so no `CommMonoid`/`AddCommMonoid` can model ▷). Witnessed by `Fate`'s two
disagreeing absorbing heads, lifted to the `fQuality` field. -/
theorem grade_mul_not_comm : ∃ a b : Grade, a * b ≠ b * a := by
  refine ⟨⟨Fate.dropped, Fate.present, Fate.present, Fate.present, Bond.intact, Merge.single⟩,
          ⟨Fate.falsified, Fate.present, Fate.present, Fate.present, Bond.intact, Merge.single⟩, ?_⟩
  decide

/-! ### Deliverable 2 — Conicality (full carrier) -/

/-- `a ▷ b = ε ⇒ a = ε ∧ b = ε`: the full carrier is conical. Deception cannot be
manufactured *from* the unit, and the unit cannot be reached *except* from itself. -/
theorem grade_conical (a b : Grade) (h : a * b = 1) : a = 1 ∧ b = 1 := by
  cases a; cases b
  simp only [mul_def, gcomp, one_def, epsilon, Grade.mk.injEq] at h
  obtain ⟨hq, hbr, hc, hr, hbo, hm⟩ := h
  obtain ⟨haq, hbq⟩ := Fate.conical _ _ hq
  obtain ⟨habr, hbbr⟩ := Fate.conical _ _ hbr
  obtain ⟨hac, hbc⟩ := Fate.conical _ _ hc
  obtain ⟨har, hbr'⟩ := Fate.conical _ _ hr
  obtain ⟨habo, hbbo⟩ := Bond.conical _ _ hbo
  obtain ⟨ham, hbm⟩ := Merge.conical _ _ hm
  constructor
  · simp only [one_def, epsilon, Grade.mk.injEq]
    exact ⟨haq, habr, hac, har, habo, ham⟩
  · simp only [one_def, epsilon, Grade.mk.injEq]
    exact ⟨hbq, hbbr, hbc, hbr', hbbo, hbm⟩

/-! ### Deliverable 3 — The honest/deceptive cancellation boundary -/

/-- **L5 — the full carrier is non-left-cancellative.** Witnessed at a deceptive
grade (`fQuality = falsified`): it absorbs any difference in the right operand's
`fQuality`, so `a ▷ x = a ▷ y` with `x ≠ y`. Cancellation here would let the lie be
subtracted back out — exactly what L5 forbids. -/
theorem grade_not_leftCancel : ∃ a x y : Grade, a * x = a * y ∧ x ≠ y := by
  refine ⟨⟨Fate.falsified, Fate.present, Fate.present, Fate.present, Bond.intact, Merge.single⟩,
          ⟨Fate.present, Fate.present, Fate.present, Fate.present, Bond.intact, Merge.single⟩,
          ⟨Fate.dropped, Fate.present, Fate.present, Fate.present, Bond.intact, Merge.single⟩, ?_⟩
  exact ⟨by decide, by decide⟩

/-- **The honest finite-fidelity region is a cancellative submonoid.** `Delta.Q`
embeds `(ℕ,+,0)` injectively and additively (`Delta.Q_add`, `Delta.Q_injective`,
`Delta.Q_zero`), and on its image right-cancellation holds — inherited from `ℕ`. This
is the cancellative core that survives the refutation of CF-as-universal. -/
theorem honest_fidelity_cancel (a b c : ℕ)
    (h : Delta.Q a + Delta.Q c = Delta.Q b + Delta.Q c) : Delta.Q a = Delta.Q b := by
  rw [Delta.Q_add, Delta.Q_add] at h
  have hac : a + c = b + c := Delta.Q_injective h
  exact congrArg Delta.Q (Nat.add_right_cancel hac)

/-- Cancellation breaks the moment fidelity reaches the deceptive bottom `Unknown`:
`Unknown ▷ Q 0 = Unknown ▷ Q 1` though `Q 0 ≠ Q 1`. (Direct from `unknown_absorbing`.) -/
theorem fidelity_unknown_not_cancel :
    Delta.unknown + Delta.Q 0 = Delta.unknown + Delta.Q 1 ∧ (Delta.Q 0 ≠ Delta.Q 1) := by
  refine ⟨by rw [Delta.unknown_absorbing, Delta.unknown_absorbing], ?_⟩
  intro h; exact absurd (Delta.Q_injective h) (by decide)

/-- Cancellation also breaks at the **honest** absorbing element `Total` — non-
deceptive, yet non-cancellative. Together with `Fate.predicated_honest_not_cancel`
and `Bond.severed_honest_not_cancel` this shows the non-cancellative set strictly
contains the deceptive set: the boundary is three-tier, not two-tier. -/
theorem fidelity_total_honest_not_cancel :
    Delta.total + Delta.Q 0 = Delta.total + Delta.Q 1 ∧ (Delta.Q 0 ≠ Delta.Q 1) := by
  refine ⟨by rw [Delta.total_add_Q, Delta.total_add_Q], ?_⟩
  intro h; exact absurd (Delta.Q_injective h) (by decide)

end Grade

end Trope

/-! ## Axiom audit (sorry-free check)

Each deliverable depends only on Lean/Mathlib's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — crucially **no `sorryAx`**. -/
section AxiomAudit
open Trope Trope.Grade
-- Deliverable 1
#print axioms Trope.Grade.instMonoid
#print axioms grade_mul_not_comm
-- Deliverable 2
#print axioms grade_conical
-- Deliverable 3
#print axioms grade_not_leftCancel
#print axioms honest_fidelity_cancel
#print axioms fidelity_unknown_not_cancel
#print axioms fidelity_total_honest_not_cancel
end AxiomAudit
