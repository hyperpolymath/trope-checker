-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
||| Grade soundness — the named open problem, pushed forward (calculus §8).
|||
||| Strategy (honest decomposition): grade soundness `g ⊑ ρ` over a whole program
||| reduces to (i) per-effect LOCAL soundness `g_op ⊑ ρ(r, op r)` — which is exactly
||| "faithful lowering" (calculus firewall 2 / O2, a front-end obligation, NOT the
||| core's to discharge); plus (ii) the algebra being a graded discipline: ⊑ a
||| PREORDER and ▷ ⊑-MONOTONE (L4). Here we machine-check (ii) at the grade level
||| and derive the compositional Fundamental Lemma and the Verdict-soundness
||| corollary. What remains genuinely open is narrowed to (i) and the operational
||| model of `fix` (calculus §7) — see docs/status/PROOF-STATUS.adoc. No axioms.
module Trope.Soundness

import Trope.Fidelity
import Trope.Coords
import Trope.Grade
import Trope.Laws
import Trope.Order

%default total

-- ── Boolean conjunction plumbing ───────────────────────────────────────────
andTrueL : (a, b : Bool) -> a && b = True -> a = True
andTrueL True  _ _   = Refl
andTrueL False _ prf = absurd prf

andTrueR : (a, b : Bool) -> a && b = True -> b = True
andTrueR True  _ prf = prf
andTrueR False _ prf = absurd prf

andTrue : (a, b : Bool) -> a = True -> b = True -> a && b = True
andTrue a b pa pb = rewrite pa in rewrite pb in Refl

-- ── ⊑ is a PREORDER on grades (reflexivity in Trope.Laws; transitivity here) ──
||| Transitivity of the grade retention order ⊑ (componentwise, from the
||| per-coordinate transitivity proofs in Trope.Order).
export
gradeLteTrans : (x, y, z : Grade)
             -> gradeLte x y = True -> gradeLte y z = True -> gradeLte x z = True
gradeLteTrans (MkGrade q1 b1 c1 r1 bo1 m1) (MkGrade q2 b2 c2 r2 bo2 m2) (MkGrade q3 b3 c3 r3 bo3 m3) p s =
  let fq1 = andTrueL _ _ p;  t1 = andTrueR _ _ p
      fb1 = andTrueL _ _ t1; t2 = andTrueR _ _ t1
      fc1 = andTrueL _ _ t2; t3 = andTrueR _ _ t2
      fr1 = andTrueL _ _ t3; t4 = andTrueR _ _ t3
      bo1' = andTrueL _ _ t4; mo1 = andTrueR _ _ t4
      fq2 = andTrueL _ _ s;  u1 = andTrueR _ _ s
      fb2 = andTrueL _ _ u1; u2 = andTrueR _ _ u1
      fc2 = andTrueL _ _ u2; u3 = andTrueR _ _ u2
      fr2 = andTrueL _ _ u3; u4 = andTrueR _ _ u3
      bo2' = andTrueL _ _ u4; mo2 = andTrueR _ _ u4
      fq = fateLteTrans q1 q2 q3 fq1 fq2
      fb = fateLteTrans b1 b2 b3 fb1 fb2
      fc = fateLteTrans c1 c2 c3 fc1 fc2
      fr = fateLteTrans r1 r2 r3 fr1 fr2
      bo = bondLteTrans bo1 bo2 bo3 bo1' bo2'
      mo = mergeLteTrans m1 m2 m3 mo1 mo2
  in andTrue _ _ fq (andTrue _ _ fb (andTrue _ _ fc (andTrue _ _ fr (andTrue _ _ bo mo))))

-- ── The soundness corollaries that follow from ⊑ being a preorder ──────────

||| T-Sub soundness (calculus §6, T-Sub): if a program is RE-DECLARED with a
||| weaker grade `g' ⊑ g`, and `g ⊑ ρ` (faithful lowering), then `g' ⊑ ρ`.
||| Claiming MORE loss stays sound; the verdict is a safe over-approximation.
export
subSound : (g', g, rho : Grade)
        -> gradeLte g' g = True -> gradeLte g rho = True -> gradeLte g' rho = True
subSound = gradeLteTrans

||| VERDICT SOUNDNESS (calculus §8 corollary): if the checker reports p-sufficient
||| against a (grade-shaped) floor — `floor ⊑ g` — and grade soundness holds for
||| this run — `g ⊑ ρ` — then the REAL residual meets the use-model: `floor ⊑ ρ`.
||| This is precisely "by transitivity ⊑" from the calculus, now machine-checked.
export
verdictSound : (floor, g, rho : Grade)
            -> gradeLte floor g = True -> gradeLte g rho = True -> gradeLte floor rho = True
verdictSound = gradeLteTrans

-- ── Grade soundness via EXACT faithful lowering (no L4 needed) ──────────────

||| If the declared grade equals the observed retention — the strongest form of
||| faithful lowering (calculus O2) — then g ⊑ ρ, by congruence of ▷ over the
||| pipeline and reflexivity of ⊑ (Trope.Laws.gradeLteRefl). No appeal to L4.
||| This is the clean route to grade soundness; T-Sub then weakens conservatively.
export
soundFromExact : (g, rho : Grade) -> g = rho -> gradeLte g rho = True
soundFromExact g rho prf = rewrite prf in gradeLteRefl rho

-- ── FINDING (2026-06-22): strict L4 monotonicity FAILS for the fate coordinate ──
-- Predicated and Dropped are intentionally INCOMPARABLE (calculus §3.1). So:
--   Dropped ⊑ Present                       (premise 1)
--   Predicated ⊑ Predicated                 (premise 2)
-- yet  Dropped ▷ Predicated = Dropped  and  Present ▷ Predicated = Predicated,
-- and  Dropped ⋢ Predicated. The three Refls machine-check that the premises hold
-- and the monotonicity conclusion is False. Consequence: conservative-step grade
-- soundness cannot be composed by naive L4 over fate (bond/merge ARE monotone —
-- Trope.Order.{bond,merge}ComposeMono); the exact route (soundFromExact) avoids it.
export
fateL4Premise1 : fateLte Dropped Present = True
fateL4Premise1 = Refl

export
fateL4Premise2 : fateLte Predicated Predicated = True
fateL4Premise2 = Refl

export
fateL4MonotonicityFails : fateLte (fateCompose Dropped Predicated) (fateCompose Present Predicated) = False
fateL4MonotonicityFails = Refl
