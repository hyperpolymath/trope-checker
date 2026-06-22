-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
||| The normative composition/order laws on the full grade (calculus §4–§5),
||| assembled componentwise from the per-coordinate proofs in Trope.Coords.
|||
|||   L1  associativity of ▷            (gradeAssoc)
|||   L2  unit (ε ▷ g = g = g ▷ ε)      (gradeUnitL, gradeUnitR)
|||   decidability of ⊑                 (decGradeLte)
|||
||| All totality-checked with no axioms or unsound escape hatches. The remaining
||| laws (L3 bottom-absorption, L4 monotonicity, L5 conflation-infectiousness)
||| hold by the bottom/absorbing structure of each coordinate (Trope.Coords);
||| grade soundness (g ⊑ ρ) is the named OPEN problem — see PROOF-STATUS.adoc.
module Trope.Laws

import Decidable.Equality
import Trope.Fidelity
import Trope.Coords
import Trope.Grade

%default total

-- L2 (gradeUnitL / gradeUnitR) is proved in Trope.Grade (ε's home module, where
-- its definition reduces) and re-exported via the import above.

||| L1: ▷ is associative on the full grade (componentwise).
export
gradeAssoc : (x, y, z : Grade)
          -> gradeCompose x (gradeCompose y z) = gradeCompose (gradeCompose x y) z
gradeAssoc (MkGrade q1 b1 c1 r1 bo1 m1) (MkGrade q2 b2 c2 r2 bo2 m2) (MkGrade q3 b3 c3 r3 bo3 m3) =
  gradeCong (fateAssoc q1 q2 q3) (fateAssoc b1 b2 b3) (fateAssoc c1 c2 c3)
            (fateAssoc r1 r2 r3) (bondAssoc bo1 bo2 bo3) (mergeAssoc m1 m2 m3)

||| The retention order ⊑ is decidable (calculus §5: each coordinate lattice has
||| decidable order, so the componentwise product order is decidable).
public export
GradeLte : Grade -> Grade -> Type
GradeLte a b = (gradeLte a b = True)

export
decGradeLte : (a, b : Grade) -> Dec (GradeLte a b)
decGradeLte a b = decEq (gradeLte a b) True

||| ⊑ is reflexive (a sanity companion to decidability).
export
gradeLteRefl : (g : Grade) -> gradeLte g g = True
gradeLteRefl (MkGrade q b c r bo m) =
  rewrite fateLteRefl q in rewrite fateLteRefl b in rewrite fateLteRefl c in
  rewrite fateLteRefl r in rewrite bondLteRefl bo in rewrite mergeLteRefl m in Refl
