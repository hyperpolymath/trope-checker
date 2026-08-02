-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
import GradeFactorisation
import GradeRatified

/-!
# Tropical factorisation — RE-RUN under the ratified carrier (R-2026-07-07, issue #29)

`GradeFactorisation.lean` answered the factorisation question against the
*pre-ratification* carrier and reached **(B) FACTORS but VERIDICALITY-BLIND**:
the collapse of `dropped` with `falsified` was *forced*, because the two heads
were a non-commuting pair and the target `Δ` is commutative
(`forced_collapse_general`). ADR 0004 (A1) removed exactly that non-commuting
pair (`Dropped ▷ Falsified = Falsified`), so the forcing argument evaporates.
This file re-runs the question against the ratified carrier
(`FateA.comp` / `GradeR` of `grade-boundary`) and the answer **changes**:

> **(B′) FACTORS AND VERIDICALITY-SIGHTED.** A nontrivial monoid homomorphism
> `πR : (GradeR, ▷, ε) → (Δ, +, Q 0)` exists (`piR_hom`, `piR_one`, bundled
> `piRHom`, `piR_nontrivial`, `piR_surjective`) **and distinguishes the honest
> `dropped` from the deceptive `falsified`** (`phiR_sighted`, `piR_sighted`):
> `Dropped ↦ ∞` (= `Delta.total`, honest total loss) vs `Falsified ↦ ⊤`
> (= `Delta.unknown`, the deceptive top). `Predicated` and `Dropped` collapse
> onto `∞` together with the honest total-loss attenuation — the hom is blind
> to *which honest* absorber acted, but no longer to *whether the absorber was
> honest*. The pre-ratification veridicality-blindness was therefore an
> **artifact of the unamended carrier**, exactly as issue #29 conjectured.

## The one repair the mechanization demanded (reported, not forced)

The naive candidate in the issue-#29 brief reads the attenuation payload off
verbatim (`atten d ↦ d`). That candidate is **not** a homomorphism on the
ratified carrier — the breaker is `atten unknown ▷ dropped = dropped`:
`πId(dropped) = ∞` but `πId(atten ⊤) + πId(dropped) = ⊤ + ∞ = ⊤ ≠ ∞`
(`phiId_not_hom` below, a verified theorem). The repair is to **squash the
deceptive payload top inside attenuation**: `squash : Δ → Δ` sends `⊤ ↦ ∞` and
is the identity elsewhere; `phiR (atten d) = squash d`. And this is not an ad
hoc dodge: `sighted_forces_squash` proves *every* veridicality-sighted
homomorphism must do something of the kind — if `f dropped ≠ f falsified` then
`f (atten ⊤) ≠ ⊤`. The trade is exact and provable: to see fate-axis
veridicality, the hom must give up separating the *payload-carried*
`total`/`unknown` distinction under `atten`. Fidelity-axis veridicality and
fate-axis veridicality cannot both ride in one commutative coordinate — but
now either *can*, which pre-ratification was false for the fate axis.
-/

namespace Trope
namespace FactorisationR

open Trope.Delta Trope.Factorisation

/-! ## The payload squash `⊤ ↦ ∞` and its arithmetic -/

/-- Squash the deceptive fidelity top into the honest one: `unknown ↦ total`,
identity on `total` and on every finite `Q n`. (`WithTop.recTopCoe` on the
outer `WithTop`.) -/
def squash (d : Delta) : Delta :=
  WithTop.recTopCoe Delta.total (fun x => ((x : WithTop ℕ) : Delta)) d

@[simp] theorem squash_top : squash Delta.unknown = Delta.total := rfl
@[simp] theorem squash_coe (x : WithTop ℕ) : squash ((x : WithTop ℕ) : Delta) = x := rfl

theorem squash_total : squash Delta.total = Delta.total := rfl
theorem squash_Q (n : ℕ) : squash (Delta.Q n) = Delta.Q n := rfl

/-- `squash 0 = 0` (needed for the unit law: `phiR (atten 0)`-shaped goals). -/
@[simp] theorem squash_zero : squash (0 : Delta) = 0 := by
  have : (0 : Delta) = ((0 : WithTop ℕ) : Delta) := by norm_cast
  rw [this, squash_coe]

/-- The squash never lands on the deceptive top. -/
theorem squash_ne_unknown (d : Delta) : squash d ≠ Delta.unknown := by
  induction d using WithTop.recTopCoe with
  | top => exact total_ne_unknown
  | coe x =>
    rw [squash_coe]
    unfold Delta.unknown
    exact WithTop.coe_ne_top

/-- `total` absorbs every squashed value: `∞ + squash d = ∞`. (This is exactly
where `squash` earns its keep — with the raw payload the `d = ⊤` case breaks.) -/
theorem total_add_squash (d : Delta) : Delta.total + squash d = Delta.total := by
  induction d using WithTop.recTopCoe with
  | top => exact total_add_total
  | coe x =>
    rw [squash_coe]
    unfold Delta.total
    rw [← WithTop.coe_add, top_add]

/-- Right-handed form: `squash d + ∞ = ∞`. -/
theorem squash_add_total (d : Delta) : squash d + Delta.total = Delta.total := by
  rw [add_comm]; exact total_add_squash d

/-- **`squash` is an additive monoid endomorphism of `Δ`**: `squash (d + e) =
squash d + squash e`. (With `squash_zero`, `squash` is a genuine `AddMonoidHom`;
this is what makes `phiR`'s `atten`-`atten` case a homomorphism case.) -/
theorem squash_add (d e : Delta) : squash (d + e) = squash d + squash e := by
  induction d using WithTop.recTopCoe with
  | top =>
    rw [top_add]
    exact (total_add_squash e).symm
  | coe x =>
    induction e using WithTop.recTopCoe with
    | top =>
      rw [add_top]
      exact (squash_add_total ((x : WithTop ℕ) : Delta)).symm
    | coe y =>
      rw [← WithTop.coe_add, squash_coe, squash_coe, squash_coe, WithTop.coe_add]

/-! ## The sighted cost `phiR` on the ratified fate, and its full-grade lift `piR` -/

/-- **The veridicality-sighted per-slot cost** on the ratified fate coordinate:

* `present ↦ 0` (forced by the unit law),
* `atten d ↦ squash d` (payload read-off, deceptive top squashed — see
  `sighted_forces_squash` for why some such squash is *mandatory*),
* `predicated ↦ ∞` and `dropped ↦ ∞` (honest absorbers: honest total loss),
* `falsified ↦ ⊤` (the deceptive top — kept apart, as (A1) now permits). -/
def phiR : Fate → Delta
  | .present    => 0
  | .atten d    => squash d
  | .predicated => Delta.total
  | .dropped    => Delta.total
  | .falsified  => Delta.unknown

@[simp] theorem phiR_present : phiR .present = 0 := rfl
@[simp] theorem phiR_atten (d : Delta) : phiR (.atten d) = squash d := rfl
@[simp] theorem phiR_predicated : phiR .predicated = Delta.total := rfl
@[simp] theorem phiR_dropped : phiR .dropped = Delta.total := rfl
@[simp] theorem phiR_falsified : phiR .falsified = Delta.unknown := rfl

/-- **`phiR` is a monoid homomorphism from the ratified fate coordinate**
(`FateA.comp`, i.e. the (A1)-amended composition) to `(Δ, +)`. Exhaustive over
all `5 × 5` constructor pairings, `atten` payloads generic. The (A1) clause
`dropped ▷ falsified = falsified` is the case that was *impossible* to pass
pre-ratification with `phi dropped ≠ phi falsified`; here it closes by
`∞ + ⊤ = ⊤` (`Delta.total_add_unknown`). -/
theorem phiR_hom (a b : Fate) : phiR (FateA.comp a b) = phiR a + phiR b := by
  cases a <;> cases b <;>
    simp [FateA.comp, phiR, squash_add, total_add_squash, squash_add_total,
          total_add_total, Delta.total_add_unknown, Delta.unknown_absorbing,
          add_unknown]

/-- Unit law at the fate level. -/
theorem phiR_one : phiR .present = 0 := rfl

/-- **The verdict-flipping disequality: `phiR dropped ≠ phiR falsified`.**
Honest withholding goes to the honest `∞`; deception goes to the deceptive
`⊤`; they are distinct (`total_ne_unknown`). Pre-ratification this exact
separation was *provably impossible* for any homomorphism into any commutative
monoid (`Factorisation.forced_collapse_general`). -/
theorem phiR_sighted : phiR .dropped ≠ phiR .falsified := total_ne_unknown

/-- What the sighted hom gives up: `predicated` and `dropped` collapse onto
`∞` (both honest absorbers). The hom sees *honest vs deceptive*, not *which
honest absorber*. -/
theorem phiR_collapses_predicated_dropped : phiR .predicated = phiR .dropped := rfl

/-- The full-grade cost `πR : GradeR → Δ`: sum the four fate-slot costs
(bond/merge contribute the additive unit, as in the pre-ratification probe). -/
def piR (g : GradeR) : Delta :=
  phiR g.fQuality + phiR g.fBearer + phiR g.fContext + phiR g.fRecord

/-- `πR ε = 0` — the unit law. -/
theorem piR_one : piR (1 : GradeR) = 0 := by
  simp [piR, GradeR.one_def, GradeR.epsilonR, phiR]

/-- **`πR (a ▷ b) = πR a + πR b`** — the homomorphism law on the ratified
grade monoid, lifted from `phiR_hom` over the four independent fate slots;
commutativity of `Δ` rearranges the eight summands (`abel`). -/
theorem piR_hom (a b : GradeR) : piR (a * b) = piR a + piR b := by
  simp only [piR, GradeR.mul_def, GradeR.gcomp, phiR_hom]
  abel

/-- Bundled: `πR` is literally a `MonoidHom` from the (now commutative!)
ratified grade monoid to `Multiplicative Δ`. -/
def piRHom : GradeR →* Multiplicative Delta where
  toFun g := Multiplicative.ofAdd (piR g)
  map_one' := by
    show Multiplicative.ofAdd (piR 1) = 1
    rw [piR_one]; rfl
  map_mul' a b := by
    show Multiplicative.ofAdd (piR (a * b)) = _
    rw [piR_hom, ofAdd_add]

/-! ## Nontriviality, surjectivity, and the grade-level sightedness -/

/-- A grade carrying fidelity `d` in its quality slot. -/
def gAttenR (d : Delta) : GradeR :=
  ⟨.atten d, .present, .present, .present, .intact, .single⟩

/-- `πR` separates attenuation levels — not the trivial collapse-to-unit. -/
theorem piR_nontrivial : piR (gAttenR (Delta.Q 1)) ≠ piR (gAttenR (Delta.Q 2)) := by
  simp only [piR, gAttenR, phiR_atten, phiR_present, add_zero, squash_Q]
  intro h; exact absurd (Delta.Q_injective h) (by decide)

/-- **`πR` is onto `Δ`**: finite and honest-∞ values through the quality slot
(`squash` is the identity there), and the deceptive `⊤` through `gFalsifiedR`. -/
theorem piR_surjective : Function.Surjective piR := by
  intro d
  induction d using WithTop.recTopCoe with
  | top =>
    refine ⟨GradeR.gFalsifiedR, ?_⟩
    simp [piR, GradeR.gFalsifiedR, phiR, Delta.unknown]
  | coe x =>
    refine ⟨gAttenR ((x : WithTop ℕ) : Delta), ?_⟩
    simp [piR, gAttenR, phiR]

/-- **Grade-level sightedness**: `πR` separates the honest-withholding grade
from the deceptive grade — the exact pair every commutative-valued hom was
forced to identify pre-ratification (`Factorisation.forced_collapse_grade`). -/
theorem piR_sighted : piR GradeR.gDroppedR ≠ piR GradeR.gFalsifiedR := by
  simp only [piR, GradeR.gDroppedR, GradeR.gFalsifiedR,
             phiR_dropped, phiR_falsified, phiR_present, add_zero]
  exact total_ne_unknown

/-! ## The naive candidate fails — reported exactly where -/

/-- The issue-#29 brief's naive candidate: payload read verbatim
(`atten d ↦ d`), `predicated, dropped ↦ ∞`, `falsified ↦ ⊤`. -/
def phiId : Fate → Delta
  | .present    => 0
  | .atten d    => d
  | .predicated => Delta.total
  | .dropped    => Delta.total
  | .falsified  => Delta.unknown

/-- **The naive candidate is NOT a homomorphism**, and this is the exact
failure point: `atten ⊤ ▷ dropped = dropped`, so the law would need
`∞ = ⊤ + ∞ = ⊤` — false. (The verbatim payload smuggles the deceptive top
into a position where the honest absorber must then swallow it.) -/
theorem phiId_not_hom :
    phiId (FateA.comp (.atten Delta.unknown) .dropped) ≠
      phiId (.atten Delta.unknown) + phiId .dropped := by
  show Delta.total ≠ Delta.unknown + Delta.total
  rw [Delta.unknown_absorbing]
  exact total_ne_unknown

/-- **The squash is forced, not a trick**: *every* multiplicative
`f : Fate → Δ` on the ratified composition that separates `dropped` from
`falsified` must keep `f (atten ⊤)` away from `⊤`. (If `f (atten ⊤) = ⊤`,
then `dropped ▷ atten ⊤ = dropped` and `falsified ▷ atten ⊤ = falsified`
both get absorbed to `⊤`, collapsing the pair.) So fate-axis sightedness
*costs* payload-top sightedness — the trade `phiR` makes is the only kind
available. -/
theorem sighted_forces_squash (f : Fate → Delta)
    (hmul : ∀ a b, f (FateA.comp a b) = f a + f b)
    (hsep : f .dropped ≠ f .falsified) :
    f (.atten Delta.unknown) ≠ Delta.unknown := by
  intro htop
  have hd : f .dropped = Delta.unknown := by
    have h := hmul .dropped (.atten Delta.unknown)
    rw [show FateA.comp .dropped (.atten Delta.unknown) = .dropped from rfl,
        htop, add_unknown] at h
    exact h
  have hf : f .falsified = Delta.unknown := by
    have h := hmul .falsified (.atten Delta.unknown)
    rw [show FateA.comp .falsified (.atten Delta.unknown) = .falsified from rfl,
        htop, add_unknown] at h
    exact h
  exact hsep (hd.trans hf.symm)

end FactorisationR
end Trope

/-! ## Axiom audit (sorry-free, axiom-clean check) -/
section AxiomAudit
open Trope.FactorisationR
-- the sighted homomorphism and its bundled form
#print axioms phiR_hom
#print axioms piR_hom
#print axioms piR_one
#print axioms piRHom
-- the verdict flip
#print axioms phiR_sighted
#print axioms piR_sighted
#print axioms phiR_collapses_predicated_dropped
-- nontriviality + surjectivity
#print axioms piR_nontrivial
#print axioms piR_surjective
-- the naive candidate's exact failure + the forced-squash trade-off
#print axioms phiId_not_hom
#print axioms sighted_forces_squash
-- squash arithmetic
#print axioms squash_add
#print axioms squash_ne_unknown
end AxiomAudit
