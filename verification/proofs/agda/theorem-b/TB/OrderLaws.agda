{-# OPTIONS --safe --without-K --cubical-compatible --exact-split #-}
-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
--
-- Theorem B — the order laws of the retention order ⊑ (TB.Order) on the
-- RATIFIED carrier (R-2026-07-07 (A2), ADR 0004).
--
--   A2-chain         Fate is a CHAIN: fateLte is reflexive, transitive,
--                    antisymmetric and total — a total order in the sense of
--                    the standard library (fate-isTotalOrder). The fidelity
--                    order dLte, which fateLte uses on the Atten segment, is a
--                    chain as well (dLte-isTotalOrder).
--   retention-order  ⊑ on grades is a decidable preorder: reflexive (TB.Order
--                    ⊑-refl), transitive (⊑-trans), decidable (⊑-dec).
--
-- TB.Order proves reflexivity only; transitivity, antisymmetry and totality
-- were stated in no ladder prover before this module (pwg.json A2-chain,
-- retention-order). Everything here is by structural case analysis on the
-- Boolean orders exactly as TB.Order defines them; no definition is changed.

module TB.OrderLaws where

open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Bool.Properties using () renaming (_≟_ to _≟ᵇ_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Structures using (IsPreorder; IsPartialOrder; IsTotalOrder)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst; isEquivalence)
open import Relation.Nullary.Decidable using (Dec)

open import TB.Grade
open import TB.Order

--------------------------------------------------------------------------------
-- ℕ: the structural Boolean ≤ (lteb) is a total order.
--------------------------------------------------------------------------------

lteb-trans : ∀ a b c → lteb a b ≡ true → lteb b c ≡ true → lteb a c ≡ true
lteb-trans zero    b       c       _ _ = refl
lteb-trans (suc a) zero    c       () _
lteb-trans (suc a) (suc b) zero    _ ()
lteb-trans (suc a) (suc b) (suc c) p q = lteb-trans a b c p q

lteb-antisym : ∀ a b → lteb a b ≡ true → lteb b a ≡ true → a ≡ b
lteb-antisym zero    zero    _ _ = refl
lteb-antisym zero    (suc b) _ ()
lteb-antisym (suc a) zero    () _
lteb-antisym (suc a) (suc b) p q = cong suc (lteb-antisym a b p q)

lteb-total : ∀ a b → lteb a b ≡ true ⊎ lteb b a ≡ true
lteb-total zero    b       = inj₁ refl
lteb-total (suc a) zero    = inj₂ refl
lteb-total (suc a) (suc b) = lteb-total a b

--------------------------------------------------------------------------------
-- Δ: the fidelity order (unknown ⊏ total ⊏ … ⊏ Q 1 ⊏ Q 0) is a total order.
--------------------------------------------------------------------------------

dLte-trans : ∀ a b c → dLte a b ≡ true → dLte b c ≡ true → dLte a c ≡ true
dLte-trans unknown b       c       _ _ = refl
dLte-trans (Q x)   (Q y)   (Q z)   p q = lteb-trans z y x q p
dLte-trans (Q x)   (Q y)   total   _ ()
dLte-trans (Q x)   (Q y)   unknown _ ()
dLte-trans (Q x)   total   c       () _
dLte-trans (Q x)   unknown c       () _
dLte-trans total   (Q y)   (Q z)   _ _ = refl
dLte-trans total   (Q y)   total   _ _ = refl
dLte-trans total   (Q y)   unknown _ ()
dLte-trans total   total   (Q z)   _ _ = refl
dLte-trans total   total   total   _ _ = refl
dLte-trans total   total   unknown _ ()
dLte-trans total   unknown c       () _

dLte-antisym : ∀ a b → dLte a b ≡ true → dLte b a ≡ true → a ≡ b
dLte-antisym unknown unknown _ _ = refl
dLte-antisym unknown (Q y)   _ ()
dLte-antisym unknown total   _ ()
dLte-antisym (Q x)   (Q y)   p q = cong Q (lteb-antisym x y q p)
dLte-antisym (Q x)   total   () _
dLte-antisym (Q x)   unknown () _
dLte-antisym total   (Q y)   _ ()
dLte-antisym total   total   _ _ = refl
dLte-antisym total   unknown () _

dLte-total : ∀ a b → dLte a b ≡ true ⊎ dLte b a ≡ true
dLte-total unknown b       = inj₁ refl
dLte-total (Q x)   (Q y)   = lteb-total y x
dLte-total (Q x)   total   = inj₂ refl
dLte-total (Q x)   unknown = inj₂ refl
dLte-total total   (Q y)   = inj₁ refl
dLte-total total   total   = inj₁ refl
dLte-total total   unknown = inj₂ refl

--------------------------------------------------------------------------------
-- A2-chain. Fate: Falsified ⊏ Dropped ⊏ Predicated ⊏ Atten(unknown) ⊏
-- Atten(total) ⊏ … ⊏ Atten(Q 0) ⊏ Present is a total order.
--------------------------------------------------------------------------------

fateLte-trans : ∀ x y z → fateLte x y ≡ true → fateLte y z ≡ true → fateLte x z ≡ true
fateLte-trans falsified  y          z          _ _ = refl
-- x = dropped: only z = falsified is open, and it forces y = falsified.
fateLte-trans dropped    y          present    _ _ = refl
fateLte-trans dropped    y          (atten _)  _ _ = refl
fateLte-trans dropped    y          predicated _ _ = refl
fateLte-trans dropped    y          dropped    _ _ = refl
fateLte-trans dropped    present    falsified  _ ()
fateLte-trans dropped    (atten _)  falsified  _ ()
fateLte-trans dropped    predicated falsified  _ ()
fateLte-trans dropped    dropped    falsified  _ ()
fateLte-trans dropped    falsified  falsified  () _
-- x = predicated: z ∈ {dropped, falsified} is refuted by y.
fateLte-trans predicated y          present    _ _ = refl
fateLte-trans predicated y          (atten _)  _ _ = refl
fateLte-trans predicated y          predicated _ _ = refl
fateLte-trans predicated present    dropped    _ ()
fateLte-trans predicated (atten _)  dropped    _ ()
fateLte-trans predicated predicated dropped    _ ()
fateLte-trans predicated dropped    dropped    () _
fateLte-trans predicated falsified  dropped    () _
fateLte-trans predicated present    falsified  _ ()
fateLte-trans predicated (atten _)  falsified  _ ()
fateLte-trans predicated predicated falsified  _ ()
fateLte-trans predicated dropped    falsified  () _
fateLte-trans predicated falsified  falsified  () _
-- x = atten a: the Atten segment is the fidelity chain.
fateLte-trans (atten a)  y          present    _ _ = refl
fateLte-trans (atten a)  present    (atten c)  _ ()
fateLte-trans (atten a)  (atten b)  (atten c)  p q = dLte-trans a b c p q
fateLte-trans (atten a)  predicated (atten c)  () _
fateLte-trans (atten a)  dropped    (atten c)  () _
fateLte-trans (atten a)  falsified  (atten c)  () _
fateLte-trans (atten a)  present    predicated _ ()
fateLte-trans (atten a)  (atten b)  predicated _ ()
fateLte-trans (atten a)  predicated predicated () _
fateLte-trans (atten a)  dropped    predicated () _
fateLte-trans (atten a)  falsified  predicated () _
fateLte-trans (atten a)  present    dropped    _ ()
fateLte-trans (atten a)  (atten b)  dropped    _ ()
fateLte-trans (atten a)  predicated dropped    () _
fateLte-trans (atten a)  dropped    dropped    () _
fateLte-trans (atten a)  falsified  dropped    () _
fateLte-trans (atten a)  present    falsified  _ ()
fateLte-trans (atten a)  (atten b)  falsified  _ ()
fateLte-trans (atten a)  predicated falsified  () _
fateLte-trans (atten a)  dropped    falsified  () _
fateLte-trans (atten a)  falsified  falsified  () _
-- x = present: present is the top, so y = present and z = present.
fateLte-trans present    y          present    _ _ = refl
fateLte-trans present    present    (atten _)  _ ()
fateLte-trans present    present    predicated _ ()
fateLte-trans present    present    dropped    _ ()
fateLte-trans present    present    falsified  _ ()
fateLte-trans present    (atten _)  (atten _)  () _
fateLte-trans present    (atten _)  predicated () _
fateLte-trans present    (atten _)  dropped    () _
fateLte-trans present    (atten _)  falsified  () _
fateLte-trans present    predicated (atten _)  () _
fateLte-trans present    predicated predicated () _
fateLte-trans present    predicated dropped    () _
fateLte-trans present    predicated falsified  () _
fateLte-trans present    dropped    (atten _)  () _
fateLte-trans present    dropped    predicated () _
fateLte-trans present    dropped    dropped    () _
fateLte-trans present    dropped    falsified  () _
fateLte-trans present    falsified  (atten _)  () _
fateLte-trans present    falsified  predicated () _
fateLte-trans present    falsified  dropped    () _
fateLte-trans present    falsified  falsified  () _

fateLte-antisym : ∀ x y → fateLte x y ≡ true → fateLte y x ≡ true → x ≡ y
fateLte-antisym present    present    _ _ = refl
fateLte-antisym present    (atten _)  () _
fateLte-antisym present    predicated () _
fateLte-antisym present    dropped    () _
fateLte-antisym present    falsified  () _
fateLte-antisym (atten a)  present    _ ()
fateLte-antisym (atten a)  (atten b)  p q = cong atten (dLte-antisym a b p q)
fateLte-antisym (atten a)  predicated () _
fateLte-antisym (atten a)  dropped    () _
fateLte-antisym (atten a)  falsified  () _
fateLte-antisym predicated present    _ ()
fateLte-antisym predicated (atten _)  _ ()
fateLte-antisym predicated predicated _ _ = refl
fateLte-antisym predicated dropped    () _
fateLte-antisym predicated falsified  () _
fateLte-antisym dropped    present    _ ()
fateLte-antisym dropped    (atten _)  _ ()
fateLte-antisym dropped    predicated _ ()
fateLte-antisym dropped    dropped    _ _ = refl
fateLte-antisym dropped    falsified  () _
fateLte-antisym falsified  present    _ ()
fateLte-antisym falsified  (atten _)  _ ()
fateLte-antisym falsified  predicated _ ()
fateLte-antisym falsified  dropped    _ ()
fateLte-antisym falsified  falsified  _ _ = refl

fateLte-total : ∀ x y → fateLte x y ≡ true ⊎ fateLte y x ≡ true
fateLte-total falsified  y          = inj₁ refl
fateLte-total present    present    = inj₁ refl
fateLte-total present    (atten _)  = inj₂ refl
fateLte-total present    predicated = inj₂ refl
fateLte-total present    dropped    = inj₂ refl
fateLte-total present    falsified  = inj₂ refl
fateLte-total (atten a)  present    = inj₁ refl
fateLte-total (atten a)  (atten b)  = dLte-total a b
fateLte-total (atten a)  predicated = inj₂ refl
fateLte-total (atten a)  dropped    = inj₂ refl
fateLte-total (atten a)  falsified  = inj₂ refl
fateLte-total predicated present    = inj₁ refl
fateLte-total predicated (atten _)  = inj₁ refl
fateLte-total predicated predicated = inj₁ refl
fateLte-total predicated dropped    = inj₂ refl
fateLte-total predicated falsified  = inj₂ refl
fateLte-total dropped    present    = inj₁ refl
fateLte-total dropped    (atten _)  = inj₁ refl
fateLte-total dropped    predicated = inj₁ refl
fateLte-total dropped    dropped    = inj₁ refl
fateLte-total dropped    falsified  = inj₂ refl

-- The relations as Set-valued orders, for the standard-library structures.
infix 4 _≤Δ_ _≤F_
_≤Δ_ : Δ → Δ → Set
a ≤Δ b = dLte a b ≡ true

_≤F_ : Fate → Fate → Set
x ≤F y = fateLte x y ≡ true

dLte-isTotalOrder : IsTotalOrder _≡_ _≤Δ_
dLte-isTotalOrder = record
  { isPartialOrder = record
    { isPreorder = record
      { isEquivalence = isEquivalence
      ; reflexive     = λ {a} {b} eq → subst (λ b′ → dLte a b′ ≡ true) eq (dLte-refl a)
      ; trans         = λ {a} {b} {c} → dLte-trans a b c
      }
    ; antisym = λ {a} {b} → dLte-antisym a b
    }
  ; total = dLte-total
  }

-- A2-chain, as one statement: Fate is a chain (a total order).
fate-isTotalOrder : IsTotalOrder _≡_ _≤F_
fate-isTotalOrder = record
  { isPartialOrder = record
    { isPreorder = record
      { isEquivalence = isEquivalence
      ; reflexive     = λ {x} {y} eq → subst (λ y′ → fateLte x y′ ≡ true) eq (fateLte-refl x)
      ; trans         = λ {x} {y} {z} → fateLte-trans x y z
      }
    ; antisym = λ {x} {y} → fateLte-antisym x y
    }
  ; total = fateLte-total
  }

--------------------------------------------------------------------------------
-- Bond and merge: chains too (Misbound ⊏ Severed ⊏ Withheld ⊏ Intact;
-- Conflated ⊏ Fused ⊏ Single). Transitivity is what ⊑-trans needs.
--------------------------------------------------------------------------------

bondLte-trans : ∀ x y z → bondLte x y ≡ true → bondLte y z ≡ true → bondLte x z ≡ true
bondLte-trans misbound y        z        _ _ = refl
bondLte-trans severed  y        intact   _ _ = refl
bondLte-trans severed  y        withheld _ _ = refl
bondLte-trans severed  y        severed  _ _ = refl
bondLte-trans severed  intact   misbound _ ()
bondLte-trans severed  withheld misbound _ ()
bondLte-trans severed  severed  misbound _ ()
bondLte-trans severed  misbound misbound () _
bondLte-trans withheld y        intact   _ _ = refl
bondLte-trans withheld y        withheld _ _ = refl
bondLte-trans withheld intact   severed  _ ()
bondLte-trans withheld withheld severed  _ ()
bondLte-trans withheld severed  severed  () _
bondLte-trans withheld misbound severed  () _
bondLte-trans withheld intact   misbound _ ()
bondLte-trans withheld withheld misbound _ ()
bondLte-trans withheld severed  misbound () _
bondLte-trans withheld misbound misbound () _
bondLte-trans intact   y        intact   _ _ = refl
bondLte-trans intact   intact   withheld _ ()
bondLte-trans intact   intact   severed  _ ()
bondLte-trans intact   intact   misbound _ ()
bondLte-trans intact   withheld z        () _
bondLte-trans intact   severed  z        () _
bondLte-trans intact   misbound z        () _

mergeLte-trans : ∀ x y z → mergeLte x y ≡ true → mergeLte y z ≡ true → mergeLte x z ≡ true
mergeLte-trans conflated y         z         _ _ = refl
mergeLte-trans fused     y         single    _ _ = refl
mergeLte-trans fused     y         fused     _ _ = refl
mergeLte-trans fused     single    conflated _ ()
mergeLte-trans fused     fused     conflated _ ()
mergeLte-trans fused     conflated conflated () _
mergeLte-trans single    y         single    _ _ = refl
mergeLte-trans single    single    fused     _ ()
mergeLte-trans single    single    conflated _ ()
mergeLte-trans single    fused     z         () _
mergeLte-trans single    conflated z         () _

--------------------------------------------------------------------------------
-- retention-order. ⊑ is the componentwise product of the six coordinate
-- orders; a Boolean conjunction of six tests, taken apart and put back.
--------------------------------------------------------------------------------

∧⁶-elim : ∀ a b c d e f → (a ∧ b ∧ c ∧ d ∧ e ∧ f) ≡ true →
          a ≡ true × b ≡ true × c ≡ true × d ≡ true × e ≡ true × f ≡ true
∧⁶-elim true  true  true  true  true  f p = refl , refl , refl , refl , refl , p
∧⁶-elim true  true  true  true  false f ()
∧⁶-elim true  true  true  false e     f ()
∧⁶-elim true  true  false d     e     f ()
∧⁶-elim true  false c     d     e     f ()
∧⁶-elim false b     c     d     e     f ()

∧⁶-intro : ∀ a b c d e f → a ≡ true → b ≡ true → c ≡ true → d ≡ true →
           e ≡ true → f ≡ true → (a ∧ b ∧ c ∧ d ∧ e ∧ f) ≡ true
∧⁶-intro true  true  true  true  true  f _  _  _  _  _  pf = pf
∧⁶-intro true  true  true  true  false f _  _  _  _  () _
∧⁶-intro true  true  true  false e     f _  _  _  () _  _
∧⁶-intro true  true  false d     e     f _  _  () _  _  _
∧⁶-intro true  false c     d     e     f _  () _  _  _  _
∧⁶-intro false b     c     d     e     f () _  _  _  _  _

⊑-trans : ∀ g h k → g ⊑ h → h ⊑ k → g ⊑ k
⊑-trans (mkGrade q₁ b₁ c₁ r₁ bo₁ m₁) (mkGrade q₂ b₂ c₂ r₂ bo₂ m₂) (mkGrade q₃ b₃ c₃ r₃ bo₃ m₃) p p′
  with ∧⁶-elim _ _ _ _ _ _ p | ∧⁶-elim _ _ _ _ _ _ p′
... | pq , pb , pc , pr , pbo , pm | pq′ , pb′ , pc′ , pr′ , pbo′ , pm′ =
  ∧⁶-intro _ _ _ _ _ _
    (fateLte-trans q₁ q₂ q₃ pq pq′)
    (fateLte-trans b₁ b₂ b₃ pb pb′)
    (fateLte-trans c₁ c₂ c₃ pc pc′)
    (fateLte-trans r₁ r₂ r₃ pr pr′)
    (bondLte-trans bo₁ bo₂ bo₃ pbo pbo′)
    (mergeLte-trans m₁ m₂ m₃ pm pm′)

-- ⊑ is decided by its own Boolean: gradeLte g h is computed, then compared.
⊑-dec : ∀ g h → Dec (g ⊑ h)
⊑-dec g h = gradeLte g h ≟ᵇ true

⊑-isPreorder : IsPreorder _≡_ _⊑_
⊑-isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = λ {g} {h} eq → subst (λ h′ → g ⊑ h′) eq (⊑-refl g)
  ; trans         = λ {g} {h} {k} → ⊑-trans g h k
  }
