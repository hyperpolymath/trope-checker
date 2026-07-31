{-# OPTIONS --safe --without-K #-}
-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
--
-- Theorem B — the retention order ⊑ (calculus §5; Order.idr / Coords.idr /
-- Fidelity.idr Boolean orders, ported verbatim, as amended by R-2026-07-07
-- (A2), ADR 0004). This is the SUBSUMPTION order used by T-Sub (leaf-only,
-- one-sided: weaken DOWNWARD in retention).
--
-- R-2026-07-07 (ADR 0004): the historical design note here ("keep ⊑ ENTIRELY
-- SEPARATE from ▷; a ▷-mono-⊑ lemma is FALSE on fate") described the
-- PRE-RATIFICATION carrier, whose {Predicated, Dropped} antichain and
-- laundering clause broke L4. On the ratified carrier the fate order is a
-- CHAIN (A2: Falsified ⊏ Dropped ⊏ Predicated ⊏ Atten(unknown) ⊏ … ⊏
-- Atten(Q 0) ⊏ Present) and ▷ IS ⊑-monotone in BOTH arguments — proved below
-- (fateL4MonoR / fateL4MonoL), mirroring Trope.Soundness.fateL4Mono{R,L}
-- (the Idris2 ground truth) and FateA.comp_mono_{right,left}
-- (verification/proofs/lean4/grade-boundary/L4Monotonicity.lean). ⊑ remains
-- the leaf-only T-Sub order in the calculus — now a design choice, not a
-- necessity. ⊑ is reflected as the Idris Boolean order (`gradeLte g h ≡
-- true`, exactly Trope.Laws.GradeLte), so it is decidable and propositional.

module TB.Order where

open import Data.Bool.Base using (Bool; true; false; _∧_; T)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import TB.Grade

-- Boolean ≤ on ℕ, structural (Idris `lte`), so reflexivity is definitional.
lteb : ℕ → ℕ → Bool
lteb zero    _       = true
lteb (suc _) zero    = false
lteb (suc m) (suc n) = lteb m n

--------------------------------------------------------------------------------
-- Per-coordinate Boolean orders (x ⊑ y  iff  "y retains at least as much as x").
--------------------------------------------------------------------------------

-- Δ: Unknown bottom; Total below finite; Q a ⊑ Q b iff b ≤ a; top is Q 0.
dLte : Δ → Δ → Bool
dLte unknown _       = true
dLte (Q a)   (Q b)   = lteb b a
dLte (Q _)   total   = false
dLte (Q _)   unknown = false
dLte total   (Q _)   = true
dLte total   total   = true
dLte total   unknown = false

-- Fate (as amended by R-2026-07-07 (A2)): a CHAIN — Falsified bottom; Dropped
-- below Predicated (A2: a checkbox retains at least as much as nothing at all;
-- the converse stays false, so a floor of Predicated still rejects Dropped);
-- Predicated below every Atten; the Atten segment ordered by δ; Present top.
fateLte : Fate → Fate → Bool
fateLte falsified  _          = true
fateLte present    present    = true
fateLte present    (atten _)  = false
fateLte present    predicated = false
fateLte present    dropped    = false
fateLte present    falsified  = false
fateLte (atten _)  present    = true
fateLte (atten a)  (atten b)  = dLte a b
fateLte (atten _)  predicated = false
fateLte (atten _)  dropped    = false
fateLte (atten _)  falsified  = false
fateLte predicated present    = true
fateLte predicated (atten _)  = true
fateLte predicated predicated = true
fateLte predicated dropped    = false
fateLte predicated falsified  = false
fateLte dropped    present    = true
fateLte dropped    (atten _)  = true
fateLte dropped    predicated = true    -- R-2026-07-07 (A2): a checkbox ⊒ nothing
fateLte dropped    dropped    = true
fateLte dropped    falsified  = false

-- Bond: Intact top; chain Intact ⊐ Withheld ⊐ Severed; Misbound bottom.
bondLte : Bond → Bond → Bool
bondLte intact   intact   = true
bondLte intact   withheld = false
bondLte intact   severed  = false
bondLte intact   misbound = false
bondLte withheld intact   = true
bondLte withheld withheld = true
bondLte withheld severed  = false
bondLte withheld misbound = false
bondLte severed  intact   = true
bondLte severed  withheld = true
bondLte severed  severed  = true
bondLte severed  misbound = false
bondLte misbound _        = true

-- Merge: Single top; Fused below; Conflated bottom.
mergeLte : Merge → Merge → Bool
mergeLte single    single    = true
mergeLte single    fused     = false
mergeLte single    conflated = false
mergeLte fused     single    = true
mergeLte fused     fused     = true
mergeLte fused     conflated = false
mergeLte conflated _         = true

-- The grade retention order: the componentwise product (Grade.idr gradeLte).
gradeLte : Grade → Grade → Bool
gradeLte (mkGrade q₁ b₁ c₁ r₁ bo₁ m₁) (mkGrade q₂ b₂ c₂ r₂ bo₂ m₂) =
  fateLte q₁ q₂ ∧ fateLte b₁ b₂ ∧ fateLte c₁ c₂ ∧ fateLte r₁ r₂
    ∧ bondLte bo₁ bo₂ ∧ mergeLte m₁ m₂

-- The Set-level subsumption relation used by T-Sub (exactly Trope.Laws.GradeLte).
infix 4 _⊑_
_⊑_ : Grade → Grade → Set
g ⊑ h = gradeLte g h ≡ true

--------------------------------------------------------------------------------
-- ⊑ is reflexive (a preorder; reflexivity is what T-Sub's identity needs).
--------------------------------------------------------------------------------

lteb-refl : ∀ n → lteb n n ≡ true
lteb-refl zero    = refl
lteb-refl (suc n) = lteb-refl n

dLte-refl : ∀ d → dLte d d ≡ true
dLte-refl (Q a)   = lteb-refl a
dLte-refl total   = refl
dLte-refl unknown = refl

fateLte-refl : ∀ f → fateLte f f ≡ true
fateLte-refl present    = refl
fateLte-refl (atten d)  = dLte-refl d
fateLte-refl predicated = refl
fateLte-refl dropped    = refl
fateLte-refl falsified  = refl

bondLte-refl : ∀ b → bondLte b b ≡ true
bondLte-refl intact   = refl
bondLte-refl withheld = refl
bondLte-refl severed  = refl
bondLte-refl misbound = refl

mergeLte-refl : ∀ m → mergeLte m m ≡ true
mergeLte-refl single    = refl
mergeLte-refl fused     = refl
mergeLte-refl conflated = refl

⊑-refl : ∀ g → g ⊑ g
⊑-refl (mkGrade q b c r bo m)
  rewrite fateLte-refl q | fateLte-refl b | fateLte-refl c | fateLte-refl r
        | bondLte-refl bo | mergeLte-refl m = refl

--------------------------------------------------------------------------------
-- L4 RESTORED on the fate coordinate (R-2026-07-07 (A1)+(A2), ADR 0004).
--
-- The 2026-06-22 finding (Soundness.idr `fateL4MonotonicityFails`, formerly
-- mirrored as TB.Tier.fate-L4-fails) — strict L4 fails on fate, witnessed at
-- the {Predicated, Dropped} antichain — is RETIRED: it is FALSE on the
-- ratified carrier, and the guard theorem is removed with it. With (A1) dropped ▷f falsified ≡ falsified and (A2) dropped ⊑
-- predicated, ▷f is ⊑-monotone in BOTH arguments. Exhaustive case analyses
-- mirroring Trope.Soundness.fateL4Mono{R,L} (Idris2 ground truth) and Lean
-- FateA.comp_mono_{right,left} (L4Monotonicity.lean); the Atten/Atten cases
-- rest on dplus monotonicity, mirroring Fidelity.idr dplusMono{R,L}.
--------------------------------------------------------------------------------

-- Chain facts replacing the retired duck-check antichain (R-2026-07-07 (A2)):
-- dropped ⊑ predicated now holds — a checkbox retains at least as much as
-- nothing at all…
fateDroppedLtePredicated : fateLte dropped predicated ≡ true
fateDroppedLtePredicated = refl

-- …while the converse stays false: a floor of predicated still rejects
-- dropped (the behavioural half of the duck check that mattered survives).
fatePredicatedNotLteDropped : fateLte predicated dropped ≡ false
fatePredicatedNotLteDropped = refl

-- ── Boolean lteb plumbing for the dplus monotonicity lemmas (Fidelity.idr
-- lteSuccRightB / lteBSelfPlus / lteBPlusLeft / ltePlusMono{Left,Right}). ──

lteb-suc-right : ∀ a b → lteb a b ≡ true → lteb a (suc b) ≡ true
lteb-suc-right zero    _       _   = refl
lteb-suc-right (suc k) zero    ()
lteb-suc-right (suc k) (suc j) prf = lteb-suc-right k j prf

lteb-self-plus : ∀ m n → lteb m (m + n) ≡ true
lteb-self-plus zero    n = refl
lteb-self-plus (suc k) n = lteb-self-plus k n

lteb-plus-left : ∀ m n → lteb n (m + n) ≡ true
lteb-plus-left zero    n = lteb-refl n
lteb-plus-left (suc k) n = lteb-suc-right n (k + n) (lteb-plus-left k n)

lteb-plus-monoL : ∀ c a b → lteb a b ≡ true → lteb (c + a) (c + b) ≡ true
lteb-plus-monoL zero    a b prf = prf
lteb-plus-monoL (suc k) a b prf = lteb-plus-monoL k a b prf

lteb-plus-monoR : ∀ a b c → lteb a b ≡ true → lteb (a + c) (b + c) ≡ true
lteb-plus-monoR zero    b       c _   = lteb-plus-left b c
lteb-plus-monoR (suc x) zero    c ()
lteb-plus-monoR (suc x) (suc y) c prf = lteb-plus-monoR x y c prf

-- ── dplus is ⊑-monotone (retention) in each argument, and adding loss on
-- either side can only lower retention (Fidelity.idr dplusMono{R,L},
-- dplusRetLte{R,L}). ──

dplusMonoR : ∀ c a b → dLte a b ≡ true → dLte (c ⊕d a) (c ⊕d b) ≡ true
dplusMonoR unknown a       b       _   = refl
dplusMonoR (Q m)   (Q x)   (Q y)   prf = lteb-plus-monoL m y x prf
dplusMonoR (Q m)   (Q x)   total   ()
dplusMonoR (Q m)   (Q x)   unknown ()
dplusMonoR (Q m)   total   (Q y)   _   = refl
dplusMonoR (Q m)   total   total   _   = refl
dplusMonoR (Q m)   total   unknown ()
dplusMonoR (Q m)   unknown (Q y)   _   = refl
dplusMonoR (Q m)   unknown total   _   = refl
dplusMonoR (Q m)   unknown unknown _   = refl
dplusMonoR total   (Q x)   (Q y)   _   = refl
dplusMonoR total   (Q x)   total   ()
dplusMonoR total   (Q x)   unknown ()
dplusMonoR total   total   (Q y)   _   = refl
dplusMonoR total   total   total   _   = refl
dplusMonoR total   total   unknown ()
dplusMonoR total   unknown (Q y)   _   = refl
dplusMonoR total   unknown total   _   = refl
dplusMonoR total   unknown unknown _   = refl

dplusMonoL : ∀ a b c → dLte a b ≡ true → dLte (a ⊕d c) (b ⊕d c) ≡ true
dplusMonoL unknown b       c       _   = refl
dplusMonoL (Q x)   (Q y)   (Q n)   prf = lteb-plus-monoR y x n prf
dplusMonoL (Q x)   (Q y)   total   _   = refl
dplusMonoL (Q x)   (Q y)   unknown _   = refl
dplusMonoL (Q x)   total   c       ()
dplusMonoL (Q x)   unknown c       ()
dplusMonoL total   (Q y)   (Q n)   _   = refl
dplusMonoL total   (Q y)   total   _   = refl
dplusMonoL total   (Q y)   unknown _   = refl
dplusMonoL total   total   (Q n)   _   = refl
dplusMonoL total   total   total   _   = refl
dplusMonoL total   total   unknown _   = refl
dplusMonoL total   unknown c       ()

-- Adding loss on the RIGHT can only lower retention: d ⊕d a ⊑ d.
dplusRetLteR : ∀ d a → dLte (d ⊕d a) d ≡ true
dplusRetLteR (Q m)   (Q n)   = lteb-self-plus m n
dplusRetLteR (Q m)   total   = refl
dplusRetLteR (Q m)   unknown = refl
dplusRetLteR total   (Q n)   = refl
dplusRetLteR total   total   = refl
dplusRetLteR total   unknown = refl
dplusRetLteR unknown a       = refl

-- Adding loss on the LEFT can only lower retention: a ⊕d e ⊑ e.
dplusRetLteL : ∀ a e → dLte (a ⊕d e) e ≡ true
dplusRetLteL (Q m)   (Q n)   = lteb-plus-left m n
dplusRetLteL (Q m)   total   = refl
dplusRetLteL (Q m)   unknown = refl
dplusRetLteL total   (Q n)   = refl
dplusRetLteL total   total   = refl
dplusRetLteL total   unknown = refl
dplusRetLteL unknown e       = refl

-- ── L4 (right argument) on fate: x ⊑ y → h ▷f x ⊑ h ▷f y. ──

fateL4MonoR : ∀ h x y → fateLte x y ≡ true → fateLte (h ▷f x) (h ▷f y) ≡ true
fateL4MonoR falsified  x          y          _   = refl
fateL4MonoR present    x          y          prf = prf
-- h = dropped: every honest tail collapses to dropped; falsified tails are
-- either absurd (x deceptive-dominated) or land on falsified ⊑ _ (A1).
fateL4MonoR dropped    falsified  y          _   = refl
fateL4MonoR dropped    present    present    _   = refl
fateL4MonoR dropped    present    (atten b)  ()
fateL4MonoR dropped    present    predicated ()
fateL4MonoR dropped    present    dropped    ()
fateL4MonoR dropped    present    falsified  ()
fateL4MonoR dropped    (atten a)  present    _   = refl
fateL4MonoR dropped    (atten a)  (atten b)  _   = refl
fateL4MonoR dropped    (atten a)  predicated ()
fateL4MonoR dropped    (atten a)  dropped    ()
fateL4MonoR dropped    (atten a)  falsified  ()
fateL4MonoR dropped    predicated present    _   = refl
fateL4MonoR dropped    predicated (atten b)  _   = refl
fateL4MonoR dropped    predicated predicated _   = refl
fateL4MonoR dropped    predicated dropped    ()
fateL4MonoR dropped    predicated falsified  ()
fateL4MonoR dropped    dropped    present    _   = refl
fateL4MonoR dropped    dropped    (atten b)  _   = refl
fateL4MonoR dropped    dropped    predicated _   = refl
fateL4MonoR dropped    dropped    dropped    _   = refl
fateL4MonoR dropped    dropped    falsified  ()
-- h = atten d: the fidelity-chain segment; atten/atten is dplus monotonicity.
fateL4MonoR (atten d)  falsified  y          _   = refl
fateL4MonoR (atten d)  present    present    _   = dLte-refl d
fateL4MonoR (atten d)  present    (atten b)  ()
fateL4MonoR (atten d)  present    predicated ()
fateL4MonoR (atten d)  present    dropped    ()
fateL4MonoR (atten d)  present    falsified  ()
fateL4MonoR (atten d)  (atten a)  present    _   = dplusRetLteR d a
fateL4MonoR (atten d)  (atten a)  (atten b)  prf = dplusMonoR d a b prf
fateL4MonoR (atten d)  (atten a)  predicated ()
fateL4MonoR (atten d)  (atten a)  dropped    ()
fateL4MonoR (atten d)  (atten a)  falsified  ()
fateL4MonoR (atten d)  predicated present    _   = refl
fateL4MonoR (atten d)  predicated (atten b)  _   = refl
fateL4MonoR (atten d)  predicated predicated _   = refl
fateL4MonoR (atten d)  predicated dropped    ()
fateL4MonoR (atten d)  predicated falsified  ()
fateL4MonoR (atten d)  dropped    present    _   = refl
fateL4MonoR (atten d)  dropped    (atten b)  _   = refl
fateL4MonoR (atten d)  dropped    predicated _   = refl
fateL4MonoR (atten d)  dropped    dropped    _   = refl
fateL4MonoR (atten d)  dropped    falsified  ()
-- h = predicated: the collapse head; the old counterexample slot
-- (x = dropped, y ⊒ predicated) now closes by (A2).
fateL4MonoR predicated falsified  y          _   = refl
fateL4MonoR predicated present    present    _   = refl
fateL4MonoR predicated present    (atten b)  ()
fateL4MonoR predicated present    predicated ()
fateL4MonoR predicated present    dropped    ()
fateL4MonoR predicated present    falsified  ()
fateL4MonoR predicated (atten a)  present    _   = refl
fateL4MonoR predicated (atten a)  (atten b)  _   = refl
fateL4MonoR predicated (atten a)  predicated ()
fateL4MonoR predicated (atten a)  dropped    ()
fateL4MonoR predicated (atten a)  falsified  ()
fateL4MonoR predicated predicated present    _   = refl
fateL4MonoR predicated predicated (atten b)  _   = refl
fateL4MonoR predicated predicated predicated _   = refl
fateL4MonoR predicated predicated dropped    ()
fateL4MonoR predicated predicated falsified  ()
fateL4MonoR predicated dropped    present    _   = refl
fateL4MonoR predicated dropped    (atten b)  _   = refl
fateL4MonoR predicated dropped    predicated _   = refl
fateL4MonoR predicated dropped    dropped    _   = refl
fateL4MonoR predicated dropped    falsified  ()

-- ── L4 (left argument) on fate: x ⊑ y → x ▷f h ⊑ y ▷f h. The x = dropped,
-- h = falsified slot is exactly where (A1) is load-bearing (both sides land
-- on falsified instead of dropped ⋢ falsified). ──

fateL4MonoL : ∀ x y h → fateLte x y ≡ true → fateLte (x ▷f h) (y ▷f h) ≡ true
fateL4MonoL falsified  y          h          _   = refl
fateL4MonoL present    present    h          _   = fateLte-refl h
fateL4MonoL present    (atten b)  h          ()
fateL4MonoL present    predicated h          ()
fateL4MonoL present    dropped    h          ()
fateL4MonoL present    falsified  h          ()
-- x = atten a
fateL4MonoL (atten a)  present    present    _   = refl
fateL4MonoL (atten a)  present    (atten e)  _   = dplusRetLteL a e
fateL4MonoL (atten a)  present    predicated _   = refl
fateL4MonoL (atten a)  present    dropped    _   = refl
fateL4MonoL (atten a)  present    falsified  _   = refl
fateL4MonoL (atten a)  (atten b)  present    prf = prf
fateL4MonoL (atten a)  (atten b)  (atten e)  prf = dplusMonoL a b e prf
fateL4MonoL (atten a)  (atten b)  predicated _   = refl
fateL4MonoL (atten a)  (atten b)  dropped    _   = refl
fateL4MonoL (atten a)  (atten b)  falsified  _   = refl
fateL4MonoL (atten a)  predicated h          ()
fateL4MonoL (atten a)  dropped    h          ()
fateL4MonoL (atten a)  falsified  h          ()
-- x = predicated
fateL4MonoL predicated present    present    _   = refl
fateL4MonoL predicated present    (atten e)  _   = refl
fateL4MonoL predicated present    predicated _   = refl
fateL4MonoL predicated present    dropped    _   = refl
fateL4MonoL predicated present    falsified  _   = refl
fateL4MonoL predicated (atten b)  present    _   = refl
fateL4MonoL predicated (atten b)  (atten e)  _   = refl
fateL4MonoL predicated (atten b)  predicated _   = refl
fateL4MonoL predicated (atten b)  dropped    _   = refl
fateL4MonoL predicated (atten b)  falsified  _   = refl
fateL4MonoL predicated predicated present    _   = refl
fateL4MonoL predicated predicated (atten e)  _   = refl
fateL4MonoL predicated predicated predicated _   = refl
fateL4MonoL predicated predicated dropped    _   = refl
fateL4MonoL predicated predicated falsified  _   = refl
fateL4MonoL predicated dropped    h          ()
fateL4MonoL predicated falsified  h          ()
-- x = dropped: (A1) closes the h = falsified slots; (A2) closes the
-- h ∈ {present, atten, predicated} slots against y ⊒ predicated.
fateL4MonoL dropped    present    present    _   = refl
fateL4MonoL dropped    present    (atten e)  _   = refl
fateL4MonoL dropped    present    predicated _   = refl
fateL4MonoL dropped    present    dropped    _   = refl
fateL4MonoL dropped    present    falsified  _   = refl
fateL4MonoL dropped    (atten b)  present    _   = refl
fateL4MonoL dropped    (atten b)  (atten e)  _   = refl
fateL4MonoL dropped    (atten b)  predicated _   = refl
fateL4MonoL dropped    (atten b)  dropped    _   = refl
fateL4MonoL dropped    (atten b)  falsified  _   = refl
fateL4MonoL dropped    predicated present    _   = refl
fateL4MonoL dropped    predicated (atten e)  _   = refl
fateL4MonoL dropped    predicated predicated _   = refl
fateL4MonoL dropped    predicated dropped    _   = refl
fateL4MonoL dropped    predicated falsified  _   = refl
fateL4MonoL dropped    dropped    h          _   = fateLte-refl (dropped ▷f h)
fateL4MonoL dropped    falsified  h          ()
