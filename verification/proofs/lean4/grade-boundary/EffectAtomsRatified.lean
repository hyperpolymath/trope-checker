-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <[REDACTED_EMAIL]>
-- SPDX-License-Identifier: MPL-2.0
import EffectAtoms
import GradeRatified

/-!
# O1 relative to the carrier, on the RATIFIED carrier `GradeR`

`EffectAtoms.lean` proves the carrier-relative half of **O1** — every grade is
the ▷-product of its six single-slot projections (`Grade.atom_factorization`),
with the projections classified into the nine atom families — over the
historical, pre-ratification `Grade`. That left an honest gap: the theorem
cited for O1-carrier was about a carrier the project no longer uses.

This module closes that gap. It states and proves the same factorisation over
`GradeR` (`GradeRatified.lean`), whose fate slots compose by the ratified
`FateA.comp` (ADR 0004, R-2026-07-07). The nine-family classification itself
(`Trope.fateFamily` / `bondFamily` / `mergeFamily`, `nine_families`,
`family_realized`, `families_disjoint`) is a classification of *coordinate
values*, and ratification changed the fate composition and order — not the
coordinate value sets — so it carries over unchanged; only the factorisation,
which is about composition, needs re-proving. The proof is the historical one
with the fate-slot unit laws swapped from `Fate.present_mul`/`mul_present` to
`FateA.one_comp`/`comp_one`.

What remains open is unchanged: **O1-coord**, whether the three coordinates
themselves are metaphysically adequate. That is a claim about the world, not
the algebra, and no theorem here touches it.
-/

namespace Trope

/-! ## Single-slot embeddings into `GradeR` -/

namespace GradeR

/-- Embed a fate value on the quality slot, all else unit. -/
def embQ (f : Fate) : GradeR := ⟨f, .present, .present, .present, .intact, .single⟩
/-- Embed a fate value on the bearer slot, all else unit. -/
def embBr (f : Fate) : GradeR := ⟨.present, f, .present, .present, .intact, .single⟩
/-- Embed a fate value on the context slot, all else unit. -/
def embC (f : Fate) : GradeR := ⟨.present, .present, f, .present, .intact, .single⟩
/-- Embed a fate value on the record slot, all else unit. -/
def embR (f : Fate) : GradeR := ⟨.present, .present, .present, f, .intact, .single⟩
/-- Embed a bond value, all else unit. -/
def embBond (b : Bond) : GradeR := ⟨.present, .present, .present, .present, b, .single⟩
/-- Embed a merge value, all else unit. -/
def embMerge (m : Merge) : GradeR := ⟨.present, .present, .present, .present, .intact, m⟩

/-- Each embedding sends its coordinate unit to the unit grade ε: a projection
at the unit value contributes nothing to the factorisation. -/
theorem embQ_one     : embQ Fate.present   = 1 := rfl
theorem embBr_one    : embBr Fate.present  = 1 := rfl
theorem embC_one     : embC Fate.present   = 1 := rfl
theorem embR_one     : embR Fate.present   = 1 := rfl
theorem embBond_one  : embBond Bond.intact = 1 := rfl
theorem embMerge_one : embMerge Merge.single = 1 := rfl

/-- **Atom factorisation on the ratified carrier (O1-carrier for `GradeR`).**
Every ratified grade is the ▷-product of its six single-slot projections.
Each projection is either ε (at a unit coordinate value, by the `emb*_one`
lemmas and `fateFamily_none_iff`/`bondFamily_none_iff`/`mergeFamily_none_iff`)
or an atom of one of the nine families, so the atoms generate the entire
ratified carrier: the effect typology is exhaustive *relative to `GradeR`*,
exactly as `Grade.atom_factorization` showed for the historical carrier. -/
theorem atom_factorization (g : GradeR) :
    g = embQ g.fQuality * embBr g.fBearer * embC g.fContext * embR g.fRecord *
        embBond g.bond * embMerge g.merge := by
  cases g
  simp [mul_def, gcomp, embQ, embBr, embC, embR, embBond, embMerge,
        FateA.one_comp, FateA.comp_one]

end GradeR

end Trope

/-! ## Axiom audit (sorryAx-free check) -/
section AxiomAudit
open Trope
#print axioms Trope.GradeR.atom_factorization
end AxiomAudit
