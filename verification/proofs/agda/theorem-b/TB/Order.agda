{-# OPTIONS --safe --without-K #-}
-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
--
-- Theorem B — the retention order ⊑ (calculus §5; Order.idr / Coords.idr /
-- Fidelity.idr Boolean orders, ported verbatim). This is the SUBSUMPTION order
-- used by T-Sub ONLY (leaf-only, one-sided: weaken DOWNWARD in retention).
--
-- DESIGN DISCIPLINE (load-bearing, per the design-panel finding and
-- Soundness.idr `fateL4MonotonicityFails`): ⊑ is kept ENTIRELY SEPARATE from
-- the non-commutative monoid ▷. There is deliberately NO `▷-mono-⊑` lemma —
-- it is FALSE on the fate coordinate (see TB.Tier.fate-L4-fails). ⊑ is reflected
-- as the Idris Boolean order (`gradeLte g h ≡ true`, exactly Trope.Laws.GradeLte),
-- so it is decidable and propositional, and is used only at the leaves.

module TB.Order where

open import Data.Bool.Base using (Bool; true; false; _∧_; T)
open import Data.Nat.Base using (ℕ; zero; suc)
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

-- Fate: Falsified bottom; Present top; Predicated/Dropped below every Atten,
-- and Predicated incomparable to Dropped (the spec's load-bearing non-chain).
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
fateLte dropped    predicated = false
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

dLte-refl : ∀ d → dLte d d ≡ true
dLte-refl (Q a)   = lteb-refl a where
  lteb-refl : ∀ n → lteb n n ≡ true
  lteb-refl zero    = refl
  lteb-refl (suc n) = lteb-refl n
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
