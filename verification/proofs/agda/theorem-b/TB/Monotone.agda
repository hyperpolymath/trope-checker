{-# OPTIONS --safe --without-K --cubical-compatible --exact-split #-}
-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
--
-- Theorem B — L4 (monotonicity) IN FULL on the RATIFIED carrier
-- (R-2026-07-07 (A1)/(A2), ADR 0004): ▷ is monotone in each argument with
-- respect to ⊑ on every coordinate, and the grade composition ▷ is too.
--
--   L4-fate        TB.Order.fateL4Mono{R,L}           (already in TB.Order)
--   L4-fidelity    TB.Order.dplusMono{R,L}            (already in TB.Order)
--   L4-bond-merge  bondL4Mono{R,L}, mergeL4Mono{R,L}  (this module)
--   L4-lifting     gradeL4Mono{R,L}, ▷-mono           (this module)
--
-- The left-argument forms follow from the right-argument forms by the
-- coordinate's commutativity (L6: ▷b-comm, ▷m-comm, grade-comm), so each
-- coordinate needs one case analysis, not two. ▷-mono, monotonicity in both
-- arguments at once, is the form the T-Fix-Decl argument (spec §7) applies at
-- a composition site; it composes the two one-sided lemmas through ⊑-trans.

module TB.Monotone where

open import Data.Bool.Base using (true)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst₂)

open import TB.Grade
open import TB.Order
open import TB.OrderLaws using (∧⁶-elim; ∧⁶-intro; ⊑-trans)

--------------------------------------------------------------------------------
-- L4-bond-merge. Bond: Misbound ⊏ Severed ⊏ Withheld ⊏ Intact.
--------------------------------------------------------------------------------

bondL4MonoR : ∀ h x y → bondLte x y ≡ true → bondLte (h ▷b x) (h ▷b y) ≡ true
bondL4MonoR intact   x        y        p = p
bondL4MonoR misbound x        y        _ = refl
bondL4MonoR withheld misbound y        _ = refl
bondL4MonoR withheld intact   intact   _ = refl
bondL4MonoR withheld intact   withheld ()
bondL4MonoR withheld intact   severed  ()
bondL4MonoR withheld intact   misbound ()
bondL4MonoR withheld withheld intact   _ = refl
bondL4MonoR withheld withheld withheld _ = refl
bondL4MonoR withheld withheld severed  ()
bondL4MonoR withheld withheld misbound ()
bondL4MonoR withheld severed  intact   _ = refl
bondL4MonoR withheld severed  withheld _ = refl
bondL4MonoR withheld severed  severed  _ = refl
bondL4MonoR withheld severed  misbound ()
bondL4MonoR severed  misbound y        _ = refl
bondL4MonoR severed  intact   intact   _ = refl
bondL4MonoR severed  intact   withheld ()
bondL4MonoR severed  intact   severed  ()
bondL4MonoR severed  intact   misbound ()
bondL4MonoR severed  withheld intact   _ = refl
bondL4MonoR severed  withheld withheld _ = refl
bondL4MonoR severed  withheld severed  ()
bondL4MonoR severed  withheld misbound ()
bondL4MonoR severed  severed  intact   _ = refl
bondL4MonoR severed  severed  withheld _ = refl
bondL4MonoR severed  severed  severed  _ = refl
bondL4MonoR severed  severed  misbound ()

bondL4MonoL : ∀ x y h → bondLte x y ≡ true → bondLte (x ▷b h) (y ▷b h) ≡ true
bondL4MonoL x y h p =
  subst₂ (λ u v → bondLte u v ≡ true) (▷b-comm h x) (▷b-comm h y) (bondL4MonoR h x y p)

-- Merge: Conflated ⊏ Fused ⊏ Single.

mergeL4MonoR : ∀ h x y → mergeLte x y ≡ true → mergeLte (h ▷m x) (h ▷m y) ≡ true
mergeL4MonoR single    x         y         p = p
mergeL4MonoR conflated x         y         _ = refl
mergeL4MonoR fused     conflated y         _ = refl
mergeL4MonoR fused     single    single    _ = refl
mergeL4MonoR fused     single    fused     ()
mergeL4MonoR fused     single    conflated ()
mergeL4MonoR fused     fused     single    _ = refl
mergeL4MonoR fused     fused     fused     _ = refl
mergeL4MonoR fused     fused     conflated ()

mergeL4MonoL : ∀ x y h → mergeLte x y ≡ true → mergeLte (x ▷m h) (y ▷m h) ≡ true
mergeL4MonoL x y h p =
  subst₂ (λ u v → mergeLte u v ≡ true) (▷m-comm h x) (▷m-comm h y) (mergeL4MonoR h x y p)

--------------------------------------------------------------------------------
-- L4-lifting. The grade composition ▷ (gradeCompose) is ⊑-monotone: the six
-- coordinate lemmas, applied componentwise.
--------------------------------------------------------------------------------

gradeL4MonoR : ∀ k g h → g ⊑ h → (k ▷ g) ⊑ (k ▷ h)
gradeL4MonoR (mkGrade q b c r bo m) (mkGrade q₁ b₁ c₁ r₁ bo₁ m₁) (mkGrade q₂ b₂ c₂ r₂ bo₂ m₂) p
  with ∧⁶-elim _ _ _ _ _ _ p
... | pq , pb , pc , pr , pbo , pm =
  ∧⁶-intro _ _ _ _ _ _
    (fateL4MonoR q q₁ q₂ pq)
    (fateL4MonoR b b₁ b₂ pb)
    (fateL4MonoR c c₁ c₂ pc)
    (fateL4MonoR r r₁ r₂ pr)
    (bondL4MonoR bo bo₁ bo₂ pbo)
    (mergeL4MonoR m m₁ m₂ pm)

gradeL4MonoL : ∀ g h k → g ⊑ h → (g ▷ k) ⊑ (h ▷ k)
gradeL4MonoL g h k p =
  subst₂ _⊑_ (grade-comm k g) (grade-comm k h) (gradeL4MonoR k g h p)

-- Both arguments at once: g₁ ⊑ g₂ and h₁ ⊑ h₂ give g₁ ▷ h₁ ⊑ g₂ ▷ h₂.
▷-mono : ∀ g₁ g₂ h₁ h₂ → g₁ ⊑ g₂ → h₁ ⊑ h₂ → (g₁ ▷ h₁) ⊑ (g₂ ▷ h₂)
▷-mono g₁ g₂ h₁ h₂ p q =
  ⊑-trans (g₁ ▷ h₁) (g₂ ▷ h₁) (g₂ ▷ h₂) (gradeL4MonoL g₁ g₂ h₁ p) (gradeL4MonoR g₂ h₁ h₂ q)
