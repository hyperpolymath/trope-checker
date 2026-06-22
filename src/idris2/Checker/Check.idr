-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
||| The checker: accumulate loss-shape grades over the IR DAG (reusing the verified
||| core's gradeCompose and the coordinate orders), then the verdict
||| floor ⊑ acc(output) with a witness edge (calculus §6, §9). `%default covering`:
||| accumulation is bounded by fuel (= #edges+1) to stay safe on a malformed cyclic
||| IR — no axioms or escape hatches.
module Checker.Check

import Data.List
import Trope.Fidelity
import Trope.Coords
import Trope.Grade
import Checker.Ir

%default covering

-- Retention meet per coordinate (the worse-retaining of two), for `fuse`.
fateMeet : Fate -> Fate -> Fate
fateMeet a b = if fateLte a b then a else if fateLte b a then b else Dropped

bondMeet : Bond -> Bond -> Bond
bondMeet a b = if bondLte a b then a else b

mergeMeet : Merge -> Merge -> Merge
mergeMeet a b = if mergeLte a b then a else b

gradeMeet : Grade -> Grade -> Grade
gradeMeet (MkGrade q1 b1 c1 r1 bo1 m1) (MkGrade q2 b2 c2 r2 bo2 m2) =
  MkGrade (fateMeet q1 q2) (fateMeet b1 b2) (fateMeet c1 c2)
          (fateMeet r1 r2) (bondMeet bo1 bo2) (mergeMeet m1 m2)

-- Accumulated grade at a node (ε at roots; ▷ along edges; meet at a fuse).
accFuel : Nat -> List Edge -> String -> Grade
accFuel Z _ _ = epsilon
accFuel (S k) edges node =
  case find (\e => e.output == node) edges of
    Nothing => epsilon
    Just e  => case map (accFuel k edges) e.inputs of
                 []          => e.egrade
                 [g]         => gradeCompose g e.egrade
                 [g1, g2]    => gradeCompose (gradeMeet g1 g2) e.egrade
                 (g :: _)    => gradeCompose g e.egrade

-- A floor coordinate is violated when the demand does not retention-≤ the residue.
chkFate : String -> Maybe Fate -> Fate -> Maybe String
chkFate name (Just d) v = if fateLte d v then Nothing else Just name
chkFate _    Nothing  _ = Nothing

chkBond : Maybe Bond -> Bond -> Maybe String
chkBond (Just d) v = if bondLte d v then Nothing else Just "bond"
chkBond Nothing  _ = Nothing

chkMerge : Maybe Merge -> Merge -> Maybe String
chkMerge (Just d) v = if mergeLte d v then Nothing else Just "merge"
chkMerge Nothing  _ = Nothing

violations : Floor -> Grade -> List String
violations fl (MkGrade q b c r bo me) = catMaybes
  [ chkFate "fate.quality" fl.fQ q, chkFate "fate.bearer" fl.fB b
  , chkFate "fate.context" fl.fC c, chkFate "fate.record" fl.fR r
  , chkBond fl.fBond bo, chkMerge fl.fMerge me ]

witnessOf : List Edge -> Floor -> List String -> Nat -> List Edge -> Maybe (String, String)
witnessOf _   _  _   _    []        = Nothing
witnessOf all fl bad fuel (e :: es) =
  let a    = accFuel fuel all e.output
      hits = filter (\c => elem c bad) (violations fl a)
  in case hits of
       (c :: _) => Just (e.eid, c)
       []       => witnessOf all fl bad fuel es

public export
data Verdict
  = Sufficient
  | Insufficient (List String) (Maybe (String, String))

export
check : Document -> Verdict
check doc =
  let fuel  = S (length doc.edges)
      final = accFuel fuel doc.edges doc.outNode
      bad   = violations doc.floor final
  in case bad of
       [] => Sufficient
       _  => Insufficient bad (witnessOf doc.edges doc.floor bad fuel doc.edges)
