{-# OPTIONS --safe --without-K #-}
-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
--
-- Theorem B, Target 3 substrate — the F4 three-tier boundary, dynamically.
--
-- The frozen F4 fact is a STATIC strict boundary cancellative-core ⊊ honest ⊊
-- full. Subject reduction must preserve it. The design-panel finding (and
-- Soundness.idr fateL4MonotonicityFails) forces the preservation to be a
-- SET-MEMBERSHIP CLOSURE property of ▷, NOT a ⊑-monotonicity, and NOT a clean
-- tier meet-homomorphism. This module establishes, in Agda, exactly which
-- closures hold and exhibits the one that FAILS:
--
--   PROVED  deceptive-absorbs-▷   : the grade-level deceptive predicate
--           (falsified/misbound/conflated — the genuine left-zeros, per
--           Veridicality.idr) is closed under ▷.  ← L5 irreversibility, dynamic.
--   PROVED  dTier-meet-hom        : the FIDELITY tier (Q/total/unknown) is a
--           meet-homomorphism for ⊕d (the clean cancellation-dimension closure).
--   PROVED  core-closed-▷         : the finite-fidelity CANCELLATIVE CORE is
--           closed under ▷ (Q embeds (ℕ,+,0)); Q-cancelʳ shows it cancels.
--   PROVED  *-not-cancel          : the L5 / honest-but-lossy non-cancellation
--           witnesses (the three-tier strictness), ported from the Lean.
--   FINDING fate-tier-meet-hom-fails : the SINGLE-TIER meet-homomorphism
--           tierOf(g▷h) ≡ tierOf g ⊓ tierOf h is FALSE on fate, witnessed by
--           `dropped ▷f falsified = dropped` (honest), an F2×F4 interaction —
--           the honest left-absorbing head `dropped` shields a later deceptive
--           operand. This is WHY tier-preservation is closure, not homomorphism.
--   GUARD   fate-L4-fails         : the L4-monotonicity tripwire (do not route
--           tier-preservation through ⊑).

module TB.Tier where

open import Data.Bool.Base using (false)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_×_; _,_; Σ; ∃)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Nat.Properties using (+-cancelʳ-≡)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans)
open import Relation.Nullary using (¬_)

open import TB.Grade
open import TB.Order using (fateLte)

--------------------------------------------------------------------------------
-- The tier lattice (deceptive ⊏ honestLossy ⊏ core) and its meet (worst-wins).
--------------------------------------------------------------------------------

data Tier : Set where
  deceptive   : Tier
  honestLossy : Tier
  core        : Tier

infixl 6 _⊓ᵗ_
_⊓ᵗ_ : Tier → Tier → Tier
deceptive   ⊓ᵗ _           = deceptive
honestLossy ⊓ᵗ deceptive   = deceptive
honestLossy ⊓ᵗ honestLossy = honestLossy
honestLossy ⊓ᵗ core        = honestLossy
core        ⊓ᵗ t           = t

-- Per-coordinate tier classifiers (lifted from the carrier, GradeBoundary §49-62:
-- falsified/misbound/conflated/unknown deceptive; dropped/predicated/severed/total
-- honest-but-lossy; finite fidelity + units the cancellative core).
dTier : Δ → Tier
dTier (Q _)   = core
dTier total   = honestLossy
dTier unknown = deceptive

fateTier : Fate → Tier
fateTier present    = core
fateTier (atten d)  = dTier d
fateTier predicated = honestLossy
fateTier dropped    = honestLossy
fateTier falsified  = deceptive

bondTier : Bond → Tier
bondTier intact   = core
bondTier withheld = honestLossy
bondTier severed  = honestLossy
bondTier misbound = deceptive

mergeTier : Merge → Tier
mergeTier single    = core
mergeTier fused     = honestLossy
mergeTier conflated = deceptive

tierOf : Grade → Tier
tierOf (mkGrade q b c r bo m) =
  fateTier q ⊓ᵗ fateTier b ⊓ᵗ fateTier c ⊓ᵗ fateTier r ⊓ᵗ bondTier bo ⊓ᵗ mergeTier m

--------------------------------------------------------------------------------
-- L5 irreversibility, DYNAMIC: the grade-level deceptive predicate is closed
-- under ▷. (Per Veridicality.idr, grade-deceptive = falsified/misbound/conflated,
-- which are the genuine left-zeros; the fidelity-unknown lives inside `atten`
-- and is handled by dTier-meet-hom, not here.)
--------------------------------------------------------------------------------

Deceptive : Grade → Set
Deceptive g = (fQuality g ≡ falsified) ⊎ (fBearer g ≡ falsified)
            ⊎ (fContext g ≡ falsified) ⊎ (fRecord g ≡ falsified)
            ⊎ (gBond g ≡ misbound) ⊎ (gMerge g ≡ conflated)

deceptive-absorbs-▷ : ∀ g h → Deceptive g → Deceptive (g ▷ h)
deceptive-absorbs-▷ (mkGrade q₁ b₁ c₁ r₁ bo₁ m₁) (mkGrade q₂ b₂ c₂ r₂ bo₂ m₂) (inj₁ eq) =
  inj₁ (cong (_▷f q₂) eq)
deceptive-absorbs-▷ (mkGrade q₁ b₁ c₁ r₁ bo₁ m₁) (mkGrade q₂ b₂ c₂ r₂ bo₂ m₂) (inj₂ (inj₁ eq)) =
  inj₂ (inj₁ (cong (_▷f b₂) eq))
deceptive-absorbs-▷ (mkGrade q₁ b₁ c₁ r₁ bo₁ m₁) (mkGrade q₂ b₂ c₂ r₂ bo₂ m₂) (inj₂ (inj₂ (inj₁ eq))) =
  inj₂ (inj₂ (inj₁ (cong (_▷f c₂) eq)))
deceptive-absorbs-▷ (mkGrade q₁ b₁ c₁ r₁ bo₁ m₁) (mkGrade q₂ b₂ c₂ r₂ bo₂ m₂) (inj₂ (inj₂ (inj₂ (inj₁ eq)))) =
  inj₂ (inj₂ (inj₂ (inj₁ (cong (_▷f r₂) eq))))
deceptive-absorbs-▷ (mkGrade q₁ b₁ c₁ r₁ bo₁ m₁) (mkGrade q₂ b₂ c₂ r₂ bo₂ m₂) (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ eq))))) =
  inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (cong (_▷b bo₂) eq)))))
deceptive-absorbs-▷ (mkGrade q₁ b₁ c₁ r₁ bo₁ m₁) (mkGrade q₂ b₂ c₂ r₂ bo₂ m₂) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ eq))))) =
  inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (cong (_▷m m₂) eq)))))

--------------------------------------------------------------------------------
-- The fidelity tier is a meet-homomorphism for ⊕d: the clean closure in the
-- cancellation dimension. (Q closed under +; total/unknown absorb downward.)
--------------------------------------------------------------------------------

dTier-meet-hom : ∀ d e → dTier (d ⊕d e) ≡ dTier d ⊓ᵗ dTier e
dTier-meet-hom (Q _)   (Q _)   = refl
dTier-meet-hom (Q _)   total   = refl
dTier-meet-hom (Q _)   unknown = refl
dTier-meet-hom total   (Q _)   = refl
dTier-meet-hom total   total   = refl
dTier-meet-hom total   unknown = refl
dTier-meet-hom unknown e       = refl

--------------------------------------------------------------------------------
-- The cancellative core (finite fidelity + units) is closed under ▷, and
-- cancels — this is tier 1, the only cancelling region.
--------------------------------------------------------------------------------

-- A finite (cancelling) fate: present, or an attenuation by a finite amount.
FinFate : Fate → Set
FinFate f = (f ≡ present) ⊎ (∃ λ n → f ≡ atten (Q n))

finfate-closed : ∀ {a b} → FinFate a → FinFate b → FinFate (a ▷f b)
finfate-closed (inj₁ refl)        fb                = fb
finfate-closed (inj₂ (n , refl))  (inj₁ refl)       = inj₂ (n , refl)
finfate-closed (inj₂ (n , refl))  (inj₂ (m , refl)) = inj₂ (n + m , refl)

-- The cancellative-core grade predicate, closed under ▷.
IsCore : Grade → Set
IsCore g = FinFate (fQuality g) × FinFate (fBearer g) × FinFate (fContext g)
         × FinFate (fRecord g) × (gBond g ≡ intact) × (gMerge g ≡ single)

core-closed-▷ : ∀ g h → IsCore g → IsCore h → IsCore (g ▷ h)
core-closed-▷ (mkGrade q₁ b₁ c₁ r₁ bo₁ m₁) (mkGrade q₂ b₂ c₂ r₂ bo₂ m₂)
  (fq₁ , fb₁ , fc₁ , fr₁ , refl , refl) (fq₂ , fb₂ , fc₂ , fr₂ , refl , refl) =
    finfate-closed fq₁ fq₂ , finfate-closed fb₁ fb₂ , finfate-closed fc₁ fc₂
  , finfate-closed fr₁ fr₂ , refl , refl

-- The core CANCELS (honest_fidelity_cancel of the Lean): on the finite image,
-- ⊕d right-cancels, inherited from ℕ.
Q-cancelʳ : ∀ a b c → (Q a ⊕d Q c) ≡ (Q b ⊕d Q c) → Q a ≡ Q b
Q-cancelʳ a b c h = cong Q (+-cancelʳ-≡ c a b (Q-inj h))

--------------------------------------------------------------------------------
-- The three-tier STRICTNESS — non-cancellation witnesses, ported clause-for-
-- clause from GradeBoundary.lean (each is a left-zero / honest-absorbing pair).
--------------------------------------------------------------------------------

-- L5, deceptive (fidelity unknown): non-left-cancellative.
unknown-not-cancel : (unknown ⊕d Q 0 ≡ unknown ⊕d Q 1) × (Q 0 ≢ Q 1)
unknown-not-cancel = refl , λ ()

-- Honest-but-lossy (fidelity total): ALSO non-cancellative (not a lie).
total-honest-not-cancel : (total ⊕d Q 0 ≡ total ⊕d Q 1) × (Q 0 ≢ Q 1)
total-honest-not-cancel = refl , λ ()

-- L5, deceptive (fate falsified): non-left-cancellative — the lie can't be subtracted out.
falsified-not-cancel : (falsified ▷f present ≡ falsified ▷f dropped) × (present ≢ dropped)
falsified-not-cancel = refl , λ ()

-- Honest withholding (fate dropped): non-cancellative, yet NOT deceptive.
dropped-honest-not-cancel : (dropped ▷f present ≡ dropped ▷f predicated) × (present ≢ predicated)
dropped-honest-not-cancel = refl , λ ()

-- Honest-but-lossy (fate predicated): collapses present and atten(Q 0).
predicated-honest-not-cancel :
    (predicated ▷f present ≡ predicated ▷f atten (Q 0)) × (present ≢ atten (Q 0))
predicated-honest-not-cancel = refl , λ ()

-- Honest-but-lossy (bond severed): non-cancellative meet element.
severed-honest-not-cancel : (severed ▷b intact ≡ severed ▷b withheld) × (intact ≢ withheld)
severed-honest-not-cancel = refl , λ ()

--------------------------------------------------------------------------------
-- THE FINDING — why tier-preservation is CLOSURE, not a homomorphism.
-- On fate, tierOf(g ▷ h) = tierOf g ⊓ tierOf h is FALSE: the honest left-
-- absorbing head `dropped` shields a later deceptive `falsified`. This is the
-- F2×F4 interaction (and the same phenomenon as fate-L4-fails below).
--------------------------------------------------------------------------------

-- dropped ▷f falsified = dropped (honestLossy), but
-- fateTier dropped ⊓ fateTier falsified = honestLossy ⊓ deceptive = deceptive.
fate-tier-meet-hom-fails :
    fateTier (dropped ▷f falsified) ≢ (fateTier dropped ⊓ᵗ fateTier falsified)
fate-tier-meet-hom-fails ()

-- The L4-monotonicity tripwire (Soundness.idr fateL4MonotonicityFails): a guard
-- so no one routes tier-preservation through ⊑. Dropped ⊑ Present and
-- Predicated ⊑ Predicated, yet Dropped▷Predicated = Dropped ⋢ Predicated.
fate-L4-fails : fateLte (dropped ▷f predicated) (present ▷f predicated) ≡ false
fate-L4-fails = refl
