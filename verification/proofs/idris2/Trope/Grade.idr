-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
||| The three-coordinate loss-shape grade (calculus §3): a field-fate over the
||| four fields Φ = {quality, bearer, context, record}, a bond, and a merge.
||| Composition ▷ and the retention order ⊑ act componentwise (calculus §4–§5).
|||
||| HC-4 (the Σ-dependency: bond coherent with the bearer's fate) is the schema's
||| job at the IR boundary (schemas/trope-ir.schema.json makes incoherent grades
||| unrepresentable). Here it is exposed as a decidable `coherent` view so the
||| core can talk about the same invariant.
module Trope.Grade

import Trope.Fidelity
import Trope.Coords

%default total

public export
record Grade where
  constructor MkGrade
  fQuality : Fate
  fBearer  : Fate
  fContext : Fate
  fRecord  : Fate
  bond     : Bond
  merge    : Merge

||| The unit grade ε (calculus §3.4): full presence on every field, intact bond,
||| no merge. `preserve` introduces it.
public export
epsilon : Grade
epsilon = MkGrade Present Present Present Present Intact Single

||| Composition ▷, componentwise (calculus §4).
public export
gradeCompose : Grade -> Grade -> Grade
gradeCompose (MkGrade q1 b1 c1 r1 bo1 m1) (MkGrade q2 b2 c2 r2 bo2 m2) =
  MkGrade (fateCompose q1 q2) (fateCompose b1 b2) (fateCompose c1 c2)
          (fateCompose r1 r2) (bondCompose bo1 bo2) (mergeCompose m1 m2)

||| Retention order ⊑ as a decidable Boolean: the componentwise product order
||| (calculus §5). True iff the right grade retains at least as much in EVERY
||| coordinate.
public export
gradeLte : Grade -> Grade -> Bool
gradeLte (MkGrade q1 b1 c1 r1 bo1 m1) (MkGrade q2 b2 c2 r2 bo2 m2) =
  fateLte q1 q2 && fateLte b1 b2 && fateLte c1 c2 && fateLte r1 r2
    && bondLte bo1 bo2 && mergeLte m1 m2

||| Is the bearer field present (not Dropped)? Drives the HC-4 coherence view.
public export
bearerPresent : Fate -> Bool
bearerPresent Dropped = False
bearerPresent _       = True

||| HC-4 coherence (the Σ-dependency, calculus §3.2): Intact/Misbound only where
||| the bearer is present; Withheld/Severed only where it is absent.
public export
coherent : Grade -> Bool
coherent g = case (bearerPresent (fBearer g), bond g) of
  (True,  Intact)   => True
  (True,  Misbound) => True
  (False, Withheld) => True
  (False, Severed)  => True
  _                 => False

||| ε is coherent (bearer present, bond Intact).
export
epsilonCoherent : coherent Grade.epsilon = True
epsilonCoherent = Refl

-- L2 (unit). The work is done against ε expanded to a literal MkGrade (so
-- gradeCompose reduces and `rewrite` sees the per-coordinate subterms); the
-- ε-stated versions follow by transporting along epsilonEq with cong/trans
-- (explicit, so no reliance on the unifier reducing ε).

||| Six-field congruence for MkGrade — lets the laws be assembled from the
||| per-coordinate proofs.
public export
gradeCong : {q1, q2, b1, b2, c1, c2, r1, r2 : Fate} -> {bo1, bo2 : Bond} -> {m1, m2 : Merge}
         -> q1 = q2 -> b1 = b2 -> c1 = c2 -> r1 = r2 -> bo1 = bo2 -> m1 = m2
         -> MkGrade q1 b1 c1 r1 bo1 m1 = MkGrade q2 b2 c2 r2 bo2 m2
gradeCong Refl Refl Refl Refl Refl Refl = Refl

-- L2 is stated with ε's literal value (which reduces under gradeCompose's
-- constructor match; a bare top-level `epsilon` as an argument does not reduce in
-- the Idris2 unifier). Since `epsilon = MkGrade Present Present Present Present
-- Intact Single` definitionally, these ARE ε ▷ g = g and g ▷ ε = g.

||| L2 (left unit): ε ▷ g = g.
export
gradeUnitL : (g : Grade)
          -> gradeCompose (MkGrade Present Present Present Present Intact Single) g = g
gradeUnitL (MkGrade q b c r bo m) =
  gradeCong (fateUnitL q) (fateUnitL b) (fateUnitL c) (fateUnitL r)
            (bondUnitL bo) (mergeUnitL m)

||| L2 (right unit): g ▷ ε = g.
export
gradeUnitR : (g : Grade)
          -> gradeCompose g (MkGrade Present Present Present Present Intact Single) = g
gradeUnitR (MkGrade q b c r bo m) =
  gradeCong (fateUnitR q) (fateUnitR b) (fateUnitR c) (fateUnitR r)
            (bondUnitR bo) (mergeUnitR m)
