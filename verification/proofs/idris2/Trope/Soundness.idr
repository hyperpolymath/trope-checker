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

-- ── L4 RESTORED for the fate coordinate (R-2026-07-07 (A1)+(A2)) ────────────
-- The 2026-06-22 finding `fateL4MonotonicityFails` (strict L4 fails on fate,
-- witnessed at the {Predicated, Dropped} antichain) is RETIRED: it is FALSE on
-- the ratified carrier. With (A1) Dropped ▷ Falsified = Falsified and (A2)
-- Dropped ⊑ Predicated, ▷ is ⊑-monotone in BOTH arguments on fate — total
-- proofs below, mirroring the Lean FateA.comp_mono_right/left development
-- (verification/proofs/lean4/grade-boundary/L4Monotonicity.lean). With
-- bond/merge monotonicity (Trope.Order.{bond,merge}ComposeMono) every
-- coordinate is now L4-monotone, so conservative-step grade soundness CAN be
-- composed by L4; the exact route (soundFromExact) remains as the strongest
-- special case.

||| Chain facts replacing the retired duck-check antichain (R-2026-07-07 (A2)):
||| Dropped ⊑ Predicated now holds — a checkbox retains at least as much as
||| nothing at all…
export
fateDroppedLtePredicated : fateLte Dropped Predicated = True
fateDroppedLtePredicated = Refl

||| …while the converse stays False: a floor of Predicated still rejects
||| Dropped (the behavioural half of the duck check that mattered survives).
export
fatePredicatedNotLteDropped : fateLte Predicated Dropped = False
fatePredicatedNotLteDropped = Refl

||| L4 (right argument) on fate: x ⊑ y → h ▷ x ⊑ h ▷ y. Exhaustive case
||| analysis; Atten/Atten needs dplus monotonicity and the loss-lowers-retention
||| lemmas from Trope.Fidelity.
export
fateL4MonoR : (h, x, y : Fate) -> fateLte x y = True -> fateLte (fateCompose h x) (fateCompose h y) = True
fateL4MonoR Falsified x y _ = Refl
fateL4MonoR Present x y prf = prf
-- h = Dropped: every honest tail collapses to Dropped; Falsified tails are
-- either absurd (x deceptive-dominated) or land on Falsified ⊑ _ (A1).
fateL4MonoR Dropped Falsified y _ = Refl
fateL4MonoR Dropped Present Present _ = Refl
fateL4MonoR Dropped Present (Atten b) prf = absurd prf
fateL4MonoR Dropped Present Predicated prf = absurd prf
fateL4MonoR Dropped Present Dropped prf = absurd prf
fateL4MonoR Dropped Present Falsified prf = absurd prf
fateL4MonoR Dropped (Atten a) Present _ = Refl
fateL4MonoR Dropped (Atten a) (Atten b) _ = Refl
fateL4MonoR Dropped (Atten a) Predicated prf = absurd prf
fateL4MonoR Dropped (Atten a) Dropped prf = absurd prf
fateL4MonoR Dropped (Atten a) Falsified prf = absurd prf
fateL4MonoR Dropped Predicated Present _ = Refl
fateL4MonoR Dropped Predicated (Atten b) _ = Refl
fateL4MonoR Dropped Predicated Predicated _ = Refl
fateL4MonoR Dropped Predicated Dropped prf = absurd prf
fateL4MonoR Dropped Predicated Falsified prf = absurd prf
fateL4MonoR Dropped Dropped Present _ = Refl
fateL4MonoR Dropped Dropped (Atten b) _ = Refl
fateL4MonoR Dropped Dropped Predicated _ = Refl
fateL4MonoR Dropped Dropped Dropped _ = Refl
fateL4MonoR Dropped Dropped Falsified prf = absurd prf
-- h = Atten d: the fidelity-chain segment; Atten/Atten is dplus monotonicity.
fateL4MonoR (Atten d) Falsified y _ = Refl
fateL4MonoR (Atten d) Present Present _ = dLteRefl d
fateL4MonoR (Atten d) Present (Atten b) prf = absurd prf
fateL4MonoR (Atten d) Present Predicated prf = absurd prf
fateL4MonoR (Atten d) Present Dropped prf = absurd prf
fateL4MonoR (Atten d) Present Falsified prf = absurd prf
fateL4MonoR (Atten d) (Atten a) Present _ = dplusRetLteR d a
fateL4MonoR (Atten d) (Atten a) (Atten b) prf = dplusMonoR d a b prf
fateL4MonoR (Atten d) (Atten a) Predicated prf = absurd prf
fateL4MonoR (Atten d) (Atten a) Dropped prf = absurd prf
fateL4MonoR (Atten d) (Atten a) Falsified prf = absurd prf
fateL4MonoR (Atten d) Predicated Present _ = Refl
fateL4MonoR (Atten d) Predicated (Atten b) _ = Refl
fateL4MonoR (Atten d) Predicated Predicated _ = Refl
fateL4MonoR (Atten d) Predicated Dropped prf = absurd prf
fateL4MonoR (Atten d) Predicated Falsified prf = absurd prf
fateL4MonoR (Atten d) Dropped Present _ = Refl
fateL4MonoR (Atten d) Dropped (Atten b) _ = Refl
fateL4MonoR (Atten d) Dropped Predicated _ = Refl
fateL4MonoR (Atten d) Dropped Dropped _ = Refl
fateL4MonoR (Atten d) Dropped Falsified prf = absurd prf
-- h = Predicated: the collapse head; the old counterexample slot
-- (x = Dropped, y ⊒ Predicated) now closes by (A2).
fateL4MonoR Predicated Falsified y _ = Refl
fateL4MonoR Predicated Present Present _ = Refl
fateL4MonoR Predicated Present (Atten b) prf = absurd prf
fateL4MonoR Predicated Present Predicated prf = absurd prf
fateL4MonoR Predicated Present Dropped prf = absurd prf
fateL4MonoR Predicated Present Falsified prf = absurd prf
fateL4MonoR Predicated (Atten a) Present _ = Refl
fateL4MonoR Predicated (Atten a) (Atten b) _ = Refl
fateL4MonoR Predicated (Atten a) Predicated prf = absurd prf
fateL4MonoR Predicated (Atten a) Dropped prf = absurd prf
fateL4MonoR Predicated (Atten a) Falsified prf = absurd prf
fateL4MonoR Predicated Predicated Present _ = Refl
fateL4MonoR Predicated Predicated (Atten b) _ = Refl
fateL4MonoR Predicated Predicated Predicated _ = Refl
fateL4MonoR Predicated Predicated Dropped prf = absurd prf
fateL4MonoR Predicated Predicated Falsified prf = absurd prf
fateL4MonoR Predicated Dropped Present _ = Refl
fateL4MonoR Predicated Dropped (Atten b) _ = Refl
fateL4MonoR Predicated Dropped Predicated _ = Refl
fateL4MonoR Predicated Dropped Dropped _ = Refl
fateL4MonoR Predicated Dropped Falsified prf = absurd prf

||| L4 (left argument) on fate: x ⊑ y → x ▷ h ⊑ y ▷ h. Exhaustive case
||| analysis; the x = Dropped, h = Falsified slot is exactly where (A1) is
||| load-bearing (both sides land on Falsified instead of Dropped ⋢ Falsified).
export
fateL4MonoL : (x, y, h : Fate) -> fateLte x y = True -> fateLte (fateCompose x h) (fateCompose y h) = True
fateL4MonoL Falsified y h _ = Refl
fateL4MonoL Present Present h _ = fateLteRefl h
fateL4MonoL Present (Atten b) h prf = absurd prf
fateL4MonoL Present Predicated h prf = absurd prf
fateL4MonoL Present Dropped h prf = absurd prf
fateL4MonoL Present Falsified h prf = absurd prf
-- x = Atten a
fateL4MonoL (Atten a) Present Present _ = Refl
fateL4MonoL (Atten a) Present (Atten e) _ = dplusRetLteL a e
fateL4MonoL (Atten a) Present Predicated _ = Refl
fateL4MonoL (Atten a) Present Dropped _ = Refl
fateL4MonoL (Atten a) Present Falsified _ = Refl
fateL4MonoL (Atten a) (Atten b) Present prf = prf
fateL4MonoL (Atten a) (Atten b) (Atten e) prf = dplusMonoL a b e prf
fateL4MonoL (Atten a) (Atten b) Predicated _ = Refl
fateL4MonoL (Atten a) (Atten b) Dropped _ = Refl
fateL4MonoL (Atten a) (Atten b) Falsified _ = Refl
fateL4MonoL (Atten a) Predicated h prf = absurd prf
fateL4MonoL (Atten a) Dropped h prf = absurd prf
fateL4MonoL (Atten a) Falsified h prf = absurd prf
-- x = Predicated
fateL4MonoL Predicated Present Present _ = Refl
fateL4MonoL Predicated Present (Atten e) _ = Refl
fateL4MonoL Predicated Present Predicated _ = Refl
fateL4MonoL Predicated Present Dropped _ = Refl
fateL4MonoL Predicated Present Falsified _ = Refl
fateL4MonoL Predicated (Atten b) Present _ = Refl
fateL4MonoL Predicated (Atten b) (Atten e) _ = Refl
fateL4MonoL Predicated (Atten b) Predicated _ = Refl
fateL4MonoL Predicated (Atten b) Dropped _ = Refl
fateL4MonoL Predicated (Atten b) Falsified _ = Refl
fateL4MonoL Predicated Predicated Present _ = Refl
fateL4MonoL Predicated Predicated (Atten e) _ = Refl
fateL4MonoL Predicated Predicated Predicated _ = Refl
fateL4MonoL Predicated Predicated Dropped _ = Refl
fateL4MonoL Predicated Predicated Falsified _ = Refl
fateL4MonoL Predicated Dropped h prf = absurd prf
fateL4MonoL Predicated Falsified h prf = absurd prf
-- x = Dropped: (A1) closes the h = Falsified slots; (A2) closes the
-- h ∈ {Present, Atten, Predicated} slots against y ⊒ Predicated.
fateL4MonoL Dropped Present Present _ = Refl
fateL4MonoL Dropped Present (Atten e) _ = Refl
fateL4MonoL Dropped Present Predicated _ = Refl
fateL4MonoL Dropped Present Dropped _ = Refl
fateL4MonoL Dropped Present Falsified _ = Refl
fateL4MonoL Dropped (Atten b) Present _ = Refl
fateL4MonoL Dropped (Atten b) (Atten e) _ = Refl
fateL4MonoL Dropped (Atten b) Predicated _ = Refl
fateL4MonoL Dropped (Atten b) Dropped _ = Refl
fateL4MonoL Dropped (Atten b) Falsified _ = Refl
fateL4MonoL Dropped Predicated Present _ = Refl
fateL4MonoL Dropped Predicated (Atten e) _ = Refl
fateL4MonoL Dropped Predicated Predicated _ = Refl
fateL4MonoL Dropped Predicated Dropped _ = Refl
fateL4MonoL Dropped Predicated Falsified _ = Refl
fateL4MonoL Dropped Dropped h _ = fateLteRefl (fateCompose Dropped h)
fateL4MonoL Dropped Falsified h prf = absurd prf
