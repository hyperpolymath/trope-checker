{-# OPTIONS --safe --without-K #-}
-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
--
-- Theorem B — headline pins. Every load-bearing theorem of each target is named
-- here via a `using` clause, so a green Smoke certifies the headlines exist with
-- the claimed types. (Same discipline as echo-types/Smoke.agda.)
module Smoke where

-- Target 1 — the grade as a NON-COMMUTATIVE graded structure (F1/F2/F3 + F4 atoms).
open import TB.Grade using
  ( Grade ; ε ; _▷_
  ; gmonoid-assoc ; gmonoid-unitL ; gmonoid-unitR   -- F1: Monoid
  ; grade-not-comm                                  -- F2: NON-commutative (mandatory)
  ; grade-conical                                   -- F3: conical
  ; falsified-absorbL ; dropped-absorbL ; misbound-absorbL ; conflated-absorbL ; unknown-absorbL )

-- Target 1 — the retention order ⊑ (T-Sub), leaf-only.
open import TB.Order using ( _⊑_ ; ⊑-refl )

-- F4 — the three-tier boundary, dynamically (closure, NOT homomorphism).
open import TB.Tier using
  ( Tier ; tierOf ; _⊓ᵗ_
  ; deceptive-absorbs-▷        -- L5 irreversibility, dynamic
  ; dTier-meet-hom            -- fidelity tier closure
  ; core-closed-▷ ; Q-cancelʳ -- cancellative core: closed + cancels
  ; unknown-not-cancel ; total-honest-not-cancel
  ; falsified-not-cancel ; dropped-honest-not-cancel
  ; predicated-honest-not-cancel ; severed-honest-not-cancel  -- three-tier strictness
  ; fate-tier-meet-hom-fails  -- THE FINDING (F2×F4)
  ; fate-L4-fails )           -- the L4 tripwire

-- Target 1 — the intrinsic graded calculus.
open import TB.Syntax using
  ( Ty ; Ctx ; _∋_ ; _⊢_!_
  ; `var ; `lam ; `app ; `letc ; `preserve ; `attenuate ; `project ; `detach ; `collapse ; `sub )

-- Target 2 — substitution / "tropes follow values through cut".
open import TB.Substitution using
  ( subst                       -- grade-EXACT value substitution lemma
  ; _[_] ; cut-preserves-grade  -- single cut, grade preserved
  ; cut-left-grade              -- oriented cut g₁ ▷ g₂
  ; cut-orientation-matters     -- REFUTATION: orientation matters (F2)
  ; cut-symmetric-fails )       -- symmetric cut impossible

-- Target 3 — subject reduction respecting the F4 tiers.
open import TB.Reduction using
  ( _↝_ ; β-app ; β-let ; reduct
  ; β-redex-grade ; let-redex-grade          -- the real SR content (unit-law collapse)
  ; β-tier-preserved ; let-tier-preserved    -- tier respected across a step
  ; attenuate-stays-deceptive ; project-stays-deceptive ; seq-stays-core )

-- Target 4 — Honest Generation (HC-*) + Veridicality (L*).
open import TB.Honest using
  ( honest-closed-▷            -- honesty closed under ▷ (the metatheorem)
  ; ε-honest ; preserve-stays-honest ; attenuate-stays-honest
  ; genFate ; genBond ; genMerge          -- HC coverage
  ; fateDeceptiveUnique ; bondDeceptiveUnique ; mergeDeceptiveUnique  -- L uniqueness
  ; deceptiveDuals )
