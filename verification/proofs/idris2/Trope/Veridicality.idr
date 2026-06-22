-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
||| The Veridicality Derivation (calculus §3.3, §6.1; HC-2c, HC-3): the loss-shape
||| grade has EXACTLY THREE deceptive duals, one per coordinate —
|||   Falsified  (false value)     on fate,
|||   Misbound   (false bearer)    on bond,
|||   Conflated  (false singleness) on merge.
||| Each is the unique deceptive inhabitant of its coordinate (characterised
||| below), and a grade is deceptive iff one of its coordinates is. Under
||| DEPLOY_VARIANT=prevent these are not writable in source; the IR schema rejects
||| any emitted deceptive grade (HC-3), so this module describes the SEMANTICS the
||| schema is the door-too-small for.
module Trope.Veridicality

import Trope.Coords
import Trope.Grade

%default total

-- The three deceptive inhabitants, one per coordinate.
public export
isDeceptiveFate : Fate -> Bool
isDeceptiveFate Falsified = True
isDeceptiveFate _         = False

public export
isDeceptiveBond : Bond -> Bool
isDeceptiveBond Misbound = True
isDeceptiveBond _        = False

public export
isDeceptiveMerge : Merge -> Bool
isDeceptiveMerge Conflated = True
isDeceptiveMerge _         = False

-- Uniqueness: each coordinate's deceptive predicate holds for exactly one value.

||| The unique deceptive fate is Falsified.
export
fateDeceptiveUnique : (f : Fate) -> isDeceptiveFate f = True -> f = Falsified
fateDeceptiveUnique Falsified _ = Refl
fateDeceptiveUnique Present   prf = absurd prf
fateDeceptiveUnique (Atten _) prf = absurd prf
fateDeceptiveUnique Predicated prf = absurd prf
fateDeceptiveUnique Dropped   prf = absurd prf

||| The unique deceptive bond is Misbound.
export
bondDeceptiveUnique : (b : Bond) -> isDeceptiveBond b = True -> b = Misbound
bondDeceptiveUnique Misbound _ = Refl
bondDeceptiveUnique Intact   prf = absurd prf
bondDeceptiveUnique Withheld prf = absurd prf
bondDeceptiveUnique Severed  prf = absurd prf

||| The unique deceptive merge is Conflated.
export
mergeDeceptiveUnique : (m : Merge) -> isDeceptiveMerge m = True -> m = Conflated
mergeDeceptiveUnique Conflated _ = Refl
mergeDeceptiveUnique Single   prf = absurd prf
mergeDeceptiveUnique Fused    prf = absurd prf

||| A grade is deceptive iff some coordinate is deceptive.
public export
deceptive : Grade -> Bool
deceptive g = isDeceptiveFate (fQuality g) || isDeceptiveFate (fBearer g)
           || isDeceptiveFate (fContext g) || isDeceptiveFate (fRecord g)
           || isDeceptiveBond (bond g) || isDeceptiveMerge (merge g)

||| ε is not deceptive (the honest baseline).
export
epsilonHonest : deceptive Grade.epsilon = False
epsilonHonest = Refl

||| The catalogue of the three deceptive duals (calculus: "exactly three"),
||| one per coordinate. This triple is total and complete by the uniqueness
||| lemmas above.
public export
deceptiveDuals : (Fate, Bond, Merge)
deceptiveDuals = (Falsified, Misbound, Conflated)
