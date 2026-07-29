-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
import GradeBoundary

/-!
# Tropical factorisation probe — does the grade admit a commutative cost-quotient?

This development **imports** the proved carrier from `grade-boundary`
(`Trope.{Delta, Fate, Bond, Merge, Grade}`) and asks a single, purely algebraic
question with **no operational model, no fix dynamics, no v0.2**:

> Is there a *nontrivial monoid homomorphism* `π : (Grade, ▷, ε) → (Δ, +, Q 0)` onto
> the commutative tropical fidelity carrier `Δ = WithTop (WithTop ℕ)` — and if so,
> what does it preserve and what does it collapse?

## Necessary-not-sufficient guard (stated verbatim, per the brief)

A POSITIVE result here means ONLY "the commutative cost-quotient EXISTS — the
tropical route is NOT EXCLUDED, precondition met." It does NOT mean "tropical solves
recursion." Whether recursion's grade actually lives in the commutative part needs an
operational model (CO-1) and stays parked. This probe can only kill the tropical
route or fail to kill it. It cannot confirm it. Nothing below touches CO-1, O4, the
limit carrier, admissibility, Scott-continuity, or `fix`/`lfp`; all of those are
downstream and out of scope.

## Ground truth reused by import (quoted from `GradeBoundary.lean`)

* `Δ = WithTop (WithTop ℕ)`, `dplus = (+)` is **commutative** (the underlying add is),
  `Q n = ↑↑n`, `total = ↑⊤` (honest ∞), `unknown = ⊤` (deceptive ⊤), unit `Q 0 = 0`.
  Absorption order is `unknown ⊐ total ⊐ finite`, with the decisive asymmetry
  `total + unknown = unknown` (`Delta.total_add_unknown`).
* `Fate.comp` is first-match (`GradeBoundary.lean` lines 126–139). `dropped` and
  `falsified` are **both** left-absorbing but disagree:
  `dropped ▷ falsified = dropped` while `falsified ▷ dropped = falsified` — the F2
  witness of non-commutativity.

## Three-way verdict reached (see the report; the Lean below is the evidence)

**(B) FACTORS but VERIDICALITY-BLIND.** A nontrivial monoid homomorphism `π` onto the
commutative `Δ` exists (`pi_hom`, `pi_one`, `pi_nontrivial`), but it necessarily
identifies the honest `dropped` with the deceptive `falsified`. The collapse is **not**
an artefact of one cost-assignment choice: *every* multiplicative map `Fate → Δ` is
forced to identify them, because `Δ` is commutative and `▷` is not (`forced_collapse`,
`no_veridicality_faithful_hom`). Hence outcome (A) — a veridicality-preserving
homomorphism — is impossible, and outcome (C) — no homomorphism at all — is false. The
tropical route captures the **fidelity** sub-grade only; specifically it is the
**fate-axis** honest/deceptive distinction (`dropped` vs `falsified`) that is forced to
collapse, because that coordinate is non-commutative. The commutative coordinates
(`Bond`, `Merge`) carry no such obstruction: their deceptive bottoms remain tropically
separable (`psiBond_hom`, `psiBond_separates_honest_deceptive`). So the blindness is
co-located exactly with the non-commutativity, on the fate axis.
-/

namespace Trope
namespace Factorisation

open Trope Trope.Delta

/-! ## A reusable right-absorption lemma on `Δ`

`grade-boundary` proves `unknown + d = unknown` (`Delta.unknown_absorbing`, the *left*
form). We also need the *right* form `d + unknown = unknown`, which is `add_top`
through the definition `unknown = ⊤`. -/

@[simp] theorem add_unknown (d : Delta) : d + Delta.unknown = Delta.unknown := by
  unfold Delta.unknown; exact add_top d

/-- `total ≠ unknown`: the honest ∞ (`↑⊤`) is a genuine coercion, the deceptive ⊤
(`⊤`) is the outer top. This single disequality is what kills the
veridicality-faithful candidate below. (Immediate from Mathlib's `WithTop.coe_ne_top`;
not a new property of the carrier, so `grade-boundary` is left untouched.) -/
theorem total_ne_unknown : Delta.total ≠ Delta.unknown := by
  unfold Delta.total Delta.unknown; exact WithTop.coe_ne_top

/-- `total + total = total`: the honest ∞ is additively idempotent (`↑⊤ + ↑⊤ = ↑⊤`).
Used by the bond-separability witness. Immediate from `WithTop.coe_add`/`top_add`. -/
theorem total_add_total : Delta.total + Delta.total = Delta.total := by
  unfold Delta.total; rw [← WithTop.coe_add, top_add]

/-- `Q n ≠ unknown`: a finite fidelity is never the deceptive top (`↑↑n ≠ ⊤`). Again a
direct `WithTop.coe_ne_top`, not a carrier extension. -/
theorem Q_ne_unknown (n : ℕ) : Delta.Q n ≠ Delta.unknown := by
  unfold Delta.Q Delta.unknown; exact WithTop.coe_ne_top

/-! # Deliverable 1 — the cost extraction `π`

The fidelity payload lives in `Fate` only (`Δ` is nested under `atten`); `Bond` and
`Merge` carry no `Δ`. So a "fidelity cost" map factors through a per-`Fate`-slot cost
`φ : Fate → Δ`, summed over the four slots, with `Bond`/`Merge` sent to the additive
unit `Q 0` (equivalently, through the constant-`0` homomorphism). This is faithful to
"extract accumulated fidelity cost".

### MODELLING CHOICES (flagged, per the brief — these are choices, not facts)

`φ present ↦ Q 0` (no loss) is the one genuinely forced value — the unit law forces it.
`φ (atten d) ↦ d` (read off the stored fidelity) is a **modelling choice**: the
canonical (faithful) representative of the additive-endomorphism family on `Δ`, any
member of which would also homomorph. The remaining assignments (absorbing and
predicated constructors) are likewise **choices**. We give **two** maps:

* `phiV` — the *veridicality-faithful* candidate: `dropped ↦ total` (honest ∞),
  `falsified ↦ unknown` (deceptive ⊤), `predicated ↦ total`. This is the natural
  first guess that tries to keep honest and deceptive apart. **It is the first place
  the probe can be gamed, and it is exactly where the probe breaks (D2).**
* `phi` — the *veridicality-blind* map: `dropped, falsified, predicated ↦ unknown`.
  This is the one that actually homomorphs (D2), and D4 shows the collapse is forced.
-/

/-- Veridicality-blind per-slot cost. The honest/deceptive distinction at
`dropped`/`falsified` is deliberately collapsed to the single absorbing top
`unknown`; D4 proves any homomorphism must do this. -/
def phi : Fate → Delta
  | .present    => Delta.Q 0
  | .atten d    => d
  | .predicated => Delta.unknown
  | .dropped    => Delta.unknown
  | .falsified  => Delta.unknown

@[simp] theorem phi_present : phi .present = 0 := by simp [phi]
@[simp] theorem phi_atten (d : Delta) : phi (.atten d) = d := rfl
@[simp] theorem phi_predicated : phi .predicated = Delta.unknown := rfl
@[simp] theorem phi_dropped : phi .dropped = Delta.unknown := rfl
@[simp] theorem phi_falsified : phi .falsified = Delta.unknown := rfl

/-- Veridicality-faithful candidate (`dropped ↦ total ≠ unknown ↦ falsified`). The
natural-but-doomed choice the brief specifies for D1; falsified in D2. -/
def phiV : Fate → Delta
  | .present    => Delta.Q 0
  | .atten d    => d
  | .predicated => Delta.total
  | .dropped    => Delta.total
  | .falsified  => Delta.unknown

/-- The full-grade cost `π : Grade → Δ`: sum the four fate-slot costs; `bond`/`merge`
contribute the additive unit (fidelity cost is carried only by the fate coordinates). -/
def pi (g : Grade) : Delta :=
  phi g.fQuality + phi g.fBearer + phi g.fContext + phi g.fRecord

/-- The veridicality-faithful full-grade cost (same shape, with `phiV`). -/
def piV (g : Grade) : Delta :=
  phiV g.fQuality + phiV g.fBearer + phiV g.fContext + phiV g.fRecord

/-! # Deliverable 2 — the homomorphism test (falsifier-first)

Two halves. **(i)** the blind `φ`/`π` *is* a homomorphism (proved green). **(ii)** the
faithful `phiV`/`piV` is *not* — exhibited by a concrete breaker at the two disagreeing
absorbing heads, exactly as predicted. -/

/-- **`φ` is a monoid homomorphism on the fate coordinate.** Proved by an *exhaustive*
case-split over all `5 × 5` constructor pairings (the `atten d` cases are handled
generically in `d`, so this is not a sampled subgrid — it discharges every pairing,
covering D6c). The non-unit cases all land on the absorbing top `unknown`, whose
left/right absorption (`unknown_absorbing`, `add_unknown`) closes them. -/
theorem phi_hom (a b : Fate) : phi (a * b) = phi a + phi b := by
  cases a <;> cases b <;>
    simp [Fate.mul_def, Fate.comp, phi, Delta.Q_zero, add_unknown,
          Delta.unknown_absorbing]

/-- **`π unit = Q 0`** — the unit law. -/
theorem pi_one : pi (1 : Grade) = Delta.Q 0 := by
  simp [pi, Grade.one_def, Grade.epsilon, phi, Delta.Q_zero]

/-- **`π (a ▷ b) = π a + π b`** — the core homomorphism, lifted from `phi_hom` over the
four independent fate slots. The rearrangement of the eight summands is exactly where
commutativity of the target `Δ` is used (`abel`); this is the algebraic content of
"the cost is a homomorphism onto a *commutative* monoid". -/
theorem pi_hom (a b : Grade) : pi (a * b) = pi a + pi b := by
  simp only [pi, Grade.mul_def, Grade.gcomp, phi_hom]
  abel

/-- **Bundled statement: `π` is literally a `MonoidHom`** from the multiplicative
grade monoid to the (additive, hence commutative) fidelity carrier viewed
multiplicatively. This makes "π is a monoid homomorphism" a typeclass-checked object,
not just a pair of equations. -/
def piHom : Grade →* Multiplicative Delta where
  toFun g := Multiplicative.ofAdd (pi g)
  map_one' := by
    show Multiplicative.ofAdd (pi 1) = 1
    rw [pi_one, Delta.Q_zero]; rfl
  map_mul' a b := by
    show Multiplicative.ofAdd (pi (a * b)) = _
    rw [pi_hom, ofAdd_add]

/-! ### D2 (falsifier side) — the veridicality-faithful candidate is NOT a homomorphism

Breaker at the two disagreeing absorbing heads. `phiV (dropped ▷ falsified) =
phiV dropped = total`, but `phiV dropped + phiV falsified = total + unknown = unknown`,
and `total ≠ unknown`. The absorbing-meet picks the constructor `dropped` by
*first-match position*, whose cost is `total`; the commutative cost-sum picks `unknown`
(the absorption-maximal top). They disagree — the cost is **entangled** with the
non-commutative constructor identity. -/

/-- Fate-level breaker for the faithful candidate. -/
theorem phiV_not_hom :
    phiV (Fate.dropped * Fate.falsified) ≠ phiV Fate.dropped + phiV Fate.falsified := by
  show Delta.total ≠ Delta.total + Delta.unknown
  rw [Delta.total_add_unknown]
  exact total_ne_unknown

/-- The two F2-witness grades (only `fQuality` departs from the unit). -/
def gDropped   : Grade := ⟨.dropped,   .present, .present, .present, .intact, .single⟩
def gFalsified : Grade := ⟨.falsified, .present, .present, .present, .intact, .single⟩

/-- **Grade-level breaker (D6a's live failing example).** The candidate `piV` fails the
homomorphism law on the F2 witness `(gDropped, gFalsified)`. -/
theorem piV_not_hom :
    piV (gDropped * gFalsified) ≠ piV gDropped + piV gFalsified := by
  simp only [piV, gDropped, gFalsified, Grade.mul_def, Grade.gcomp, Fate.mul_def,
             Fate.comp, phiV, Delta.Q_zero, add_zero, zero_add]
  rw [Delta.total_add_unknown]
  exact total_ne_unknown

/-! # Deliverable 3 — nontriviality

`φ` (hence `π`) distinguishes attenuation levels, so it is not the trivial
collapse-to-unit. Guarded against a vacuous YES. -/

/-- `φ` separates distinct finite fidelities. -/
theorem phi_nontrivial : phi (.atten (Delta.Q 1)) ≠ phi (.atten (Delta.Q 2)) := by
  show Delta.Q 1 ≠ Delta.Q 2
  intro h; exact absurd (Delta.Q_injective h) (by decide)

/-- A grade carrying fidelity `d` in its quality slot. -/
def gAtten (d : Delta) : Grade := ⟨.atten d, .present, .present, .present, .intact, .single⟩

/-- **`π` is nontrivial**: it separates `atten (Q 1)` from `atten (Q 2)` at grade level. -/
theorem pi_nontrivial : pi (gAtten (Delta.Q 1)) ≠ pi (gAtten (Delta.Q 2)) := by
  simp only [pi, gAtten, phi_atten, phi_present, add_zero]
  intro h; exact absurd (Delta.Q_injective h) (by decide)

/-- **`π` is onto** (so "onto Δ" in the prose is literal, not loose): every fidelity `d`
is realised by the grade carrying `d` in its quality slot. `π (gAtten d) = d`. -/
theorem pi_surjective : Function.Surjective pi := by
  intro d
  refine ⟨gAtten d, ?_⟩
  simp only [pi, gAtten, phi_atten, phi_present, add_zero]

/-- **Nontriviality is not merely an `atten`-coercion artefact**: `π` already separates
the unit grade from the honest-withholding grade on the *discrete* part
(`π ε = Q 0 ≠ unknown = π gDropped`). Defends against the "too degenerate to count as
factoring" objection. -/
theorem pi_discrete_nontrivial : pi (1 : Grade) ≠ pi gDropped := by
  rw [pi_one]
  simp only [pi, gDropped, phi_dropped, phi_present, add_zero]
  exact Q_ne_unknown 0

/-! # Deliverable 4 — veridicality discrimination, and why the collapse is FORCED

The sharp result. We do not merely observe that *our* `φ` collapses `dropped` and
`falsified`; we prove that **every** multiplicative map `Fate → Δ` must. The argument
needs only multiplicativity and commutativity of `Δ` — not `map_one`, not any choice
of costs. -/

/-- **Impossibility of veridicality-faithfulness — against ANY commutative target.**
For *any* commutative monoid `M` and *any* multiplicative `f : Fate → M`
(`f (a * b) = f a + f b`), necessarily `f dropped = f falsified`. The two composites
`dropped ▷ falsified = dropped` and `falsified ▷ dropped = falsified` force
`f dropped = f dropped + f falsified` and `f falsified = f falsified + f dropped`;
commutativity of `M` makes the right-hand sides equal, hence so are the left-hand
sides. This uses *only* commutativity of the target — so the obstruction is not special
to the chosen `Δ`; **no** commutative cost-carrier whatsoever can separate the honest
`dropped` from the deceptive `falsified` while respecting composition. This is the F2
non-commutativity meeting the commutativity of the target, in its sharpest form. -/
theorem forced_collapse_general {M : Type*} [AddCommMonoid M] (f : Fate → M)
    (hmul : ∀ a b, f (a * b) = f a + f b) :
    f Fate.dropped = f Fate.falsified := by
  have h1 : f Fate.dropped = f Fate.dropped + f Fate.falsified := by
    have := hmul Fate.dropped Fate.falsified
    rwa [show Fate.dropped * Fate.falsified = Fate.dropped from rfl] at this
  have h2 : f Fate.falsified = f Fate.dropped + f Fate.falsified := by
    have := hmul Fate.falsified Fate.dropped
    rw [show Fate.falsified * Fate.dropped = Fate.falsified from rfl] at this
    rwa [add_comm] at this
  exact h1.trans h2.symm

/-- The `Δ`-specialisation actually used by the corollaries below. -/
theorem forced_collapse (f : Fate → Delta)
    (hmul : ∀ a b, f (a * b) = f a + f b) :
    f Fate.dropped = f Fate.falsified :=
  forced_collapse_general f hmul

/-- **No veridicality-faithful homomorphism exists.** There is no multiplicative
`Fate → Δ` that keeps the honest `dropped` apart from the deceptive `falsified`. This
rules out the best-case outcome (A) unconditionally. -/
theorem no_veridicality_faithful_hom :
    ¬ ∃ f : Fate → Delta,
        (∀ a b, f (a * b) = f a + f b) ∧ f Fate.dropped ≠ f Fate.falsified := by
  rintro ⟨f, hmul, hsep⟩
  exact hsep (forced_collapse f hmul)

/-- **Grade-level, fold-agnostic form.** ANY multiplicative `f : Grade → M` into ANY
commutative monoid `M` identifies the honest-withholding grade `gDropped` with the
deceptive grade `gFalsified` — because those two grades are *themselves* a non-commuting
pair (`gDropped ▷ gFalsified = gDropped`, `gFalsified ▷ gDropped = gFalsified`, both by
`decide`). This is the mechanised backing for "no choice of how to fold the four slots,
the bond, and the merge — sum or otherwise, into `Δ` or any other commutative target —
recovers the distinction". -/
theorem forced_collapse_grade {M : Type*} [AddCommMonoid M] (f : Grade → M)
    (hmul : ∀ a b, f (a * b) = f a + f b) :
    f gDropped = f gFalsified := by
  have e1 : gDropped * gFalsified = gDropped := by decide
  have e2 : gFalsified * gDropped = gFalsified := by decide
  have h1 : f gDropped = f gDropped + f gFalsified := by rw [← e1]; exact hmul _ _
  have h2 : f gFalsified = f gFalsified + f gDropped := by rw [← e2]; exact hmul _ _
  rw [add_comm] at h2
  exact h1.trans h2.symm

/-- Our chosen `φ` *is* blind (it realises the forced collapse). -/
theorem phi_blind : phi Fate.dropped = phi Fate.falsified := rfl

/-- Grade-level statement of the blindness: `π` cannot tell the honest withholding
grade from the deceptive grade. -/
theorem pi_collapses_honest_deceptive : pi gDropped = pi gFalsified := by
  simp [pi, gDropped, gFalsified, phi]

/-! ### The blindness is LOCALISED to the fate axis (the non-commutative coordinate)

The forced collapse is a property of `Fate` specifically — the coordinate with *two*
disagreeing absorbing heads. `Bond` and `Merge` are **commutative** monoids (proved in
`grade-boundary`), so there is no F2-style obstruction there and their deceptive bottoms
*are* tropically separable. The following exhibits a genuine (unital) homomorphism
`Bond → Δ` that keeps the deceptive bottom `misbound` apart from the honest absorbing
`severed`. Hence `π` drops bond/merge veridicality only as a *modelling choice*
(`π` ignores those coordinates), whereas the **fate** honest/deceptive distinction is
collapsed by *necessity*. Conclusion: tropical loses precisely the fate-axis
veridicality, not veridicality wholesale. -/

/-- A cost map on the (commutative) bond coordinate: honest chain `intact, withheld ↦ 0`,
honest disconnection `severed ↦ total`, deceptive `misbound ↦ unknown`. -/
def psiBond : Bond → Delta
  | .intact   => Delta.Q 0
  | .withheld => Delta.Q 0
  | .severed  => Delta.total
  | .misbound => Delta.unknown

/-- `psiBond` is a genuine monoid homomorphism (`Bond` is commutative, so this goes
through cleanly — no absorbing-head disagreement to obstruct it). -/
theorem psiBond_hom (a b : Bond) : psiBond (a * b) = psiBond a + psiBond b := by
  cases a <;> cases b <;>
    simp [Bond.mul_def, Bond.comp, psiBond, Delta.Q_zero, add_unknown,
          Delta.unknown_absorbing, Delta.total_add_unknown, total_add_total]

/-- … and it **separates** the deceptive `misbound` from the honest `severed`
(`total ≠ unknown`). So bond-veridicality survives the tropical projection — the loss is
specific to the fate axis. -/
theorem psiBond_separates_honest_deceptive :
    psiBond Bond.severed ≠ psiBond Bond.misbound := total_ne_unknown

/-! # Deliverable 5 — the complement: F2 non-commutativity lives entirely in `ker`-direction

Because the target is commutative, `π` is blind to **all** non-commutativity, the F2
witness included. We state the general fact and then confirm it on the F2 witness,
alongside the witness's genuine non-commutativity (so the confinement is not vacuous). -/

/-- **`π` cannot see non-commutativity at all**: `π (a ▷ b) = π (b ▷ a)` for every
`a, b`. Immediate from `pi_hom` and commutativity of `Δ`. Hence whatever
non-commutativity the carrier has is confined to the complement of `π` (it never
reaches the cost-quotient). -/
theorem pi_blind_to_noncomm (a b : Grade) : pi (a * b) = pi (b * a) := by
  rw [pi_hom, pi_hom, add_comm]

/-- The F2 witness is genuinely non-commutative (`a ▷ b ≠ b ▷ a`) … -/
theorem grade_F2_noncomm : gDropped * gFalsified ≠ gFalsified * gDropped := by decide

/-- … yet `π` identifies the two composites: the non-commutativity is invisible to the
cost-quotient, i.e. it lives entirely in the complement. -/
theorem pi_collapses_F2 : pi (gDropped * gFalsified) = pi (gFalsified * gDropped) :=
  pi_blind_to_noncomm gDropped gFalsified

/-! # Deliverable 6 — falsifier harness

* 6a — `piV_not_hom` (above) is the live failing example surfaced by `just falsify`.
* 6b — the trivial map (everything ↦ `Q 0`) *is* a homomorphism but *fails*
  nontriviality, so D3 is doing real work, not decoration.
* 6c — `phi_hom` is by exhaustive `cases a <;> cases b` (every pairing, `atten`
  generic), so no absorbing-head pairing is sampled away. `phi_hom_heads` re-exposes
  the pure-head subgrid explicitly. -/

/-- The trivial collapse-to-unit map. -/
def phi0 : Fate → Delta := fun _ => Delta.Q 0

/-- 6b — the trivial map *is* a homomorphism. -/
theorem phi0_hom (a b : Fate) : phi0 (a * b) = phi0 a + phi0 b := by
  simp [phi0, Delta.Q_zero]

/-- 6b — … but it *fails* nontriviality: it cannot separate attenuation levels. So a
"YES" that came only from collapsing everything would be caught by D3. -/
theorem phi0_not_nontrivial : phi0 (.atten (Delta.Q 1)) = phi0 (.atten (Delta.Q 2)) := rfl

/-- 6c — the absorbing-head subgrid, stated explicitly over all pairings of the four
non-`atten` heads; each follows from the exhaustive `phi_hom`. -/
theorem phi_hom_heads :
    ∀ a ∈ [Fate.present, Fate.predicated, Fate.dropped, Fate.falsified],
    ∀ b ∈ [Fate.present, Fate.predicated, Fate.dropped, Fate.falsified],
      phi (a * b) = phi a + phi b :=
  fun a _ b _ => phi_hom a b

end Factorisation
end Trope

/-! ## Axiom audit (sorry-free, axiom-clean check)

Every deliverable depends only on Lean/Mathlib's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`) — crucially **no `sorryAx`**, no user `axiom`, no
`native`-kernel `decide` bypass. `just falsify` greps the source and this audit for
violations. (Plain `decide`, as used here and throughout `grade-boundary`, runs in the
trusted kernel and is permitted; only the `native` compiled-evaluator bypass is not.) -/
section AxiomAudit
open Trope.Factorisation
-- D2: the homomorphism and its bundled form
#print axioms pi_hom
#print axioms pi_one
#print axioms piHom
-- D2 falsifier: the faithful candidate breaks
#print axioms phiV_not_hom
#print axioms piV_not_hom
-- D3: nontriviality (+ surjectivity, discrete separation)
#print axioms pi_nontrivial
#print axioms pi_surjective
#print axioms pi_discrete_nontrivial
-- D4: forced collapse / impossibility of (A)
#print axioms forced_collapse_general
#print axioms forced_collapse
#print axioms forced_collapse_grade
#print axioms no_veridicality_faithful_hom
#print axioms pi_collapses_honest_deceptive
-- D4 localisation: bond-veridicality IS tropically separable
#print axioms psiBond_hom
#print axioms psiBond_separates_honest_deceptive
-- D5: complement / F2 confinement
#print axioms pi_blind_to_noncomm
#print axioms grade_F2_noncomm
#print axioms pi_collapses_F2
-- D6: trivial-map adversary
#print axioms phi0_hom
#print axioms phi0_not_nontrivial
#print axioms phi_hom_heads
end AxiomAudit
