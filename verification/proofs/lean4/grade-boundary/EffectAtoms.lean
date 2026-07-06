-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
import GradeBoundary

/-!
# O1 relative to the carrier: atom factorization and the nine effect families

Spec v0.1 §10 leaves **O1** open: is the effect typology exhaustive, or merely a
well-chosen list? This file settles the *carrier-relative* half of that
question as a theorem. (The other half — whether the three-coordinate carrier
itself captures every way particularity can be lost — is a metaphysical
adequacy claim, not provable inside the algebra; it stays open as O1-coord.)

**Definitions.** An *atom* is a grade that differs from ε in exactly one
coordinate. Atoms come in **nine families**, one per non-unit coordinate value
kind:

| family      | coordinate  | value        | vocabulary effect            |
|-------------|-------------|--------------|------------------------------|
| attenuate   | fate        | `Atten δ`    | `p-attenuating`              |
| collapse    | fate        | `Predicated` | `p-collapsing`               |
| drop        | fate        | `Dropped`    | `p-projecting` (field clause)|
| falsify     | fate        | `Falsified`  | `p-falsifying`               |
| withhold    | bond        | `Withheld`   | `p-projecting` (bearer clause)|
| sever       | bond        | `Severed`    | `p-detaching`                |
| misbind     | bond        | `Misbound`   | `p-misbinding`               |
| fuse        | merge       | `Fused`      | `p-fusing`                   |
| conflate    | merge       | `Conflated`  | `p-conflating`               |

with `p-preserving` = ε = the empty product.

**Theorems.**
* `Fintype.card AtomFamily = 9` (`nine_families`).
* Every grade factors as the product of its six single-coordinate projections
  (`atom_factorization`) — so the atoms *generate* the full carrier, and the
  vocabulary's effect list is exhaustive **relative to the carrier**: there is
  no way to move in the grade monoid that is not a composite of the nine
  families.
* Every family is inhabited by an atom (`family_realized`), so none of the nine
  is redundant.

**A vocabulary observation this makes precise:** the nine *families* and the
nine *vocabulary effects* do not align one-to-one. `p-preserving` names the
empty product; `p-projecting` covers *two* families (`drop` on a fate field,
`withhold` on the bond); the `withhold` family has no standalone effect name.
That is a naming seam, not an algebra gap — recorded here so O1's residue is
exactly the metaphysical adequacy question.
-/

namespace Trope

/-! ## Single-coordinate embeddings -/

namespace Grade

/-- Embed a fate value on the quality field, all else unit. -/
def embQ (f : Fate) : Grade := ⟨f, .present, .present, .present, .intact, .single⟩
/-- Embed a fate value on the bearer field, all else unit. -/
def embBr (f : Fate) : Grade := ⟨.present, f, .present, .present, .intact, .single⟩
/-- Embed a fate value on the context field, all else unit. -/
def embC (f : Fate) : Grade := ⟨.present, .present, f, .present, .intact, .single⟩
/-- Embed a fate value on the record field, all else unit. -/
def embR (f : Fate) : Grade := ⟨.present, .present, .present, f, .intact, .single⟩
/-- Embed a bond value, all else unit. -/
def embBond (b : Bond) : Grade := ⟨.present, .present, .present, .present, b, .single⟩
/-- Embed a merge value, all else unit. -/
def embMerge (m : Merge) : Grade := ⟨.present, .present, .present, .present, .intact, m⟩

/-- **Atom factorization.** Every grade is the ▷-product of its six
single-coordinate projections. Since each projection is either the unit or an
atom of one of the nine families, the atoms generate the entire carrier. -/
theorem atom_factorization (g : Grade) :
    g = embQ g.fQuality * embBr g.fBearer * embC g.fContext * embR g.fRecord *
        embBond g.bond * embMerge g.merge := by
  cases g
  simp [mul_def, gcomp, embQ, embBr, embC, embR, embBond, embMerge]

end Grade

/-! ## The nine families -/

/-- The nine atom families of the three-coordinate carrier. -/
inductive AtomFamily
  | attenuate | collapse | drop | falsify   -- fate (per field)
  | withhold | sever | misbind              -- bond
  | fuse | conflate                         -- merge
deriving DecidableEq, Repr, Fintype

/-- There are exactly nine atom families. -/
theorem nine_families : Fintype.card AtomFamily = 9 := rfl

/-- Family of a non-unit fate value. -/
def fateFamily : Fate → Option AtomFamily
  | .present => none
  | .atten _ => some .attenuate
  | .predicated => some .collapse
  | .dropped => some .drop
  | .falsified => some .falsify

/-- Family of a non-unit bond value. -/
def bondFamily : Bond → Option AtomFamily
  | .intact => none
  | .withheld => some .withhold
  | .severed => some .sever
  | .misbound => some .misbind

/-- Family of a non-unit merge value. -/
def mergeFamily : Merge → Option AtomFamily
  | .single => none
  | .fused => some .fuse
  | .conflated => some .conflate

/-- A coordinate value maps to `none` exactly when it is the coordinate unit:
the classification is total on non-unit values. -/
theorem fateFamily_none_iff (f : Fate) : fateFamily f = none ↔ f = .present := by
  cases f <;> simp [fateFamily]
theorem bondFamily_none_iff (b : Bond) : bondFamily b = none ↔ b = .intact := by
  cases b <;> simp [bondFamily]
theorem mergeFamily_none_iff (m : Merge) : mergeFamily m = none ↔ m = .single := by
  cases m <;> simp [mergeFamily]

/-- **Every family is realized** by a coordinate value — none of the nine is
redundant. -/
theorem family_realized : ∀ fam : AtomFamily,
    (∃ f : Fate, fateFamily f = some fam) ∨
    (∃ b : Bond, bondFamily b = some fam) ∨
    (∃ m : Merge, mergeFamily m = some fam) := by
  intro fam
  cases fam with
  | attenuate => exact Or.inl ⟨.atten (Delta.Q 1), rfl⟩
  | collapse => exact Or.inl ⟨.predicated, rfl⟩
  | drop => exact Or.inl ⟨.dropped, rfl⟩
  | falsify => exact Or.inl ⟨.falsified, rfl⟩
  | withhold => exact Or.inr (Or.inl ⟨.withheld, rfl⟩)
  | sever => exact Or.inr (Or.inl ⟨.severed, rfl⟩)
  | misbind => exact Or.inr (Or.inl ⟨.misbound, rfl⟩)
  | fuse => exact Or.inr (Or.inr ⟨.fused, rfl⟩)
  | conflate => exact Or.inr (Or.inr ⟨.conflated, rfl⟩)

/-- Which coordinate a family belongs to: fate ↦ 0, bond ↦ 1, merge ↦ 2. -/
def coordOf : AtomFamily → ℕ
  | .attenuate | .collapse | .drop | .falsify => 0
  | .withhold | .sever | .misbind => 1
  | .fuse | .conflate => 2

theorem fateFamily_coord (f : Fate) (fam : AtomFamily)
    (h : fateFamily f = some fam) : coordOf fam = 0 := by
  cases f <;> simp [fateFamily] at h <;> simp [← h, coordOf]

theorem bondFamily_coord (b : Bond) (fam : AtomFamily)
    (h : bondFamily b = some fam) : coordOf fam = 1 := by
  cases b <;> simp [bondFamily] at h <;> simp [← h, coordOf]

theorem mergeFamily_coord (m : Merge) (fam : AtomFamily)
    (h : mergeFamily m = some fam) : coordOf fam = 2 := by
  cases m <;> simp [mergeFamily] at h <;> simp [← h, coordOf]

/-- The three classifiers hit disjoint family sets: a fate family is never a
bond or merge family and vice versa — the nine families partition cleanly by
coordinate (4 + 3 + 2 = 9). -/
theorem families_disjoint :
    (∀ (f : Fate) (b : Bond) fam, fateFamily f = some fam → bondFamily b ≠ some fam) ∧
    (∀ (f : Fate) (m : Merge) fam, fateFamily f = some fam → mergeFamily m ≠ some fam) ∧
    (∀ (b : Bond) (m : Merge) fam, bondFamily b = some fam → mergeFamily m ≠ some fam) := by
  refine ⟨fun f b fam hf hb => ?_, fun f m fam hf hm => ?_, fun b m fam hb hm => ?_⟩
  · have h1 := fateFamily_coord f fam hf
    have h2 := bondFamily_coord b fam hb
    omega
  · have h1 := fateFamily_coord f fam hf
    have h2 := mergeFamily_coord m fam hm
    omega
  · have h1 := bondFamily_coord b fam hb
    have h2 := mergeFamily_coord m fam hm
    omega

end Trope

/-! ## Axiom audit (sorry-free check) -/
section AxiomAudit
open Trope
#print axioms Trope.Grade.atom_factorization
#print axioms Trope.nine_families
#print axioms Trope.family_realized
#print axioms Trope.families_disjoint
#print axioms Trope.fateFamily_none_iff
end AxiomAudit
