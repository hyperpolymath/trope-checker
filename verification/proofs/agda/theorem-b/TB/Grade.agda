{-# OPTIONS --safe --without-K #-}
-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
--
-- Theorem B, Target 1 — the trope-particularity grade algebra as a
-- NON-COMMUTATIVE graded structure, in Agda, --safe --without-K.
--
-- This module ports the FROZEN INTERFACE (Lean source of truth
-- verification/proofs/lean4/grade-boundary/GradeBoundary.lean, sorry-free,
-- axioms propext/Quot.sound only) constructor-for-constructor and
-- clause-for-clause, re-establishing the four established facts in Agda so
-- the calculus metatheory (Syntax/Reduction) can be built ON TOP of a grade
-- object whose non-commutativity (F2) is intrinsic and whose three-tier
-- boundary (F4) is available as a structural predicate.
--
--   F1  Grade is a product Monoid (componentwise)           — gmonoid-{assoc,unitL,unitR}
--   F2  the product is NON-COMMUTATIVE                       — grade-not-comm
--   F3  conicality on the full carrier                       — grade-conical
--   F4  three-tier strict boundary                           — §F4 below
--       deceptive (left zeros ⇒ non-left-cancellative, L5), honest-but-lossy
--       (still non-cancellative), cancellative core (finite fidelity, Q embeds ℕ).
--
-- Reuses the STYLE of echo-types/proofs/agda/EchoGraded.agda (a thin-poset
-- reindexing modality: a decidable, propositional order with a degrade action)
-- — the retention order ⊑ lives in TB.Order in that exact spirit.

module TB.Grade where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-cancelʳ-≡)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (¬_)

--------------------------------------------------------------------------------
-- Fidelity carrier  Δ = WithTop (WithTop ℕ)  (Fidelity.idr / GradeBoundary.lean)
--   Q n      finite quantified loss  (Q 0 is the unit; the honest, cancelling core)
--   total    ∞ honest total loss      (inner ⊤: absorbs finite, NOT a lie)
--   unknown  loss of unknown amount   (outer ⊤: the deceptive bottom of fidelity = L5)
-- dplus is the WithTop (+): finite adds; both tops absorb (unknown ⊐ total ⊐ finite).
--------------------------------------------------------------------------------

data Δ : Set where
  Q       : ℕ → Δ
  total   : Δ
  unknown : Δ

infixl 6 _⊕d_
_⊕d_ : Δ → Δ → Δ
unknown ⊕d _       = unknown
total   ⊕d unknown = unknown
total   ⊕d total   = total
total   ⊕d Q _     = total
Q _     ⊕d unknown = unknown
Q _     ⊕d total   = total
Q a     ⊕d Q b     = Q (a + b)

-- Q is injective: distinct finite losses are distinct fidelities.
Q-inj : ∀ {a b} → Q a ≡ Q b → a ≡ b
Q-inj refl = refl

-- dplus is associative (15-clause case split; only Q/Q/Q is non-refl).
⊕d-assoc : ∀ a b c → a ⊕d (b ⊕d c) ≡ (a ⊕d b) ⊕d c
⊕d-assoc unknown b       c       = refl
⊕d-assoc total   unknown c       = refl
⊕d-assoc total   total   unknown = refl
⊕d-assoc total   total   total   = refl
⊕d-assoc total   total   (Q _)   = refl
⊕d-assoc total   (Q _)   unknown = refl
⊕d-assoc total   (Q _)   total   = refl
⊕d-assoc total   (Q _)   (Q _)   = refl
⊕d-assoc (Q _)   unknown c       = refl
⊕d-assoc (Q _)   total   unknown = refl
⊕d-assoc (Q _)   total   total   = refl
⊕d-assoc (Q _)   total   (Q _)   = refl
⊕d-assoc (Q _)   (Q _)   unknown = refl
⊕d-assoc (Q _)   (Q _)   total   = refl
⊕d-assoc (Q a)   (Q b)   (Q c)   = cong Q (sym (+-assoc a b c))

-- Q 0 is the two-sided unit.
⊕d-unitL : ∀ d → Q 0 ⊕d d ≡ d
⊕d-unitL (Q _)   = refl
⊕d-unitL total   = refl
⊕d-unitL unknown = refl

⊕d-unitR : ∀ d → d ⊕d Q 0 ≡ d
⊕d-unitR (Q a)   = cong Q (+-identityʳ a)
⊕d-unitR total   = refl
⊕d-unitR unknown = refl

-- L5 (fidelity): unknown is a (two-sided) absorbing element — unknown loss is
-- irrecoverable. (Left form is the one the boundary keys on.)
unknown-absorbL : ∀ d → unknown ⊕d d ≡ unknown
unknown-absorbL _ = refl

-- total absorbs finite (honest, not a lie) but is itself absorbed by unknown.
total-absorb-Q : ∀ n → total ⊕d Q n ≡ total
total-absorb-Q _ = refl

total-⊕d-unknown : total ⊕d unknown ≡ unknown
total-⊕d-unknown = refl

--------------------------------------------------------------------------------
-- Coordinate 1 — field fate  (Coords.idr §3.1 / GradeBoundary.lean Fate.comp)
-- A NON-COMMUTATIVE monoid: present is the unit; falsified (deceptive bottom)
-- and dropped (honest withholding) are BOTH left-absorbing but disagree, which
-- is the source of F2. Clause-for-clause, first-match, exactly as the Lean.
--------------------------------------------------------------------------------

data Fate : Set where
  present    : Fate
  atten      : Δ → Fate
  predicated : Fate
  dropped    : Fate
  falsified  : Fate

infixl 7 _▷f_
_▷f_ : Fate → Fate → Fate
falsified  ▷f _          = falsified
dropped    ▷f _          = dropped
present    ▷f f          = f
atten _    ▷f falsified  = falsified
atten _    ▷f dropped    = dropped
atten d    ▷f present    = atten d
atten d    ▷f atten e    = atten (d ⊕d e)
atten _    ▷f predicated = predicated
predicated ▷f falsified  = falsified
predicated ▷f dropped    = dropped
predicated ▷f present    = predicated
predicated ▷f atten _    = predicated
predicated ▷f predicated = predicated

-- F1 (fate): associativity. The ONLY non-refl clause is atten/atten/atten.
▷f-assoc : ∀ a b c → a ▷f (b ▷f c) ≡ (a ▷f b) ▷f c
▷f-assoc falsified  _          _          = refl
▷f-assoc dropped    _          _          = refl
▷f-assoc present    _          _          = refl
▷f-assoc (atten _)  falsified  _          = refl
▷f-assoc (atten _)  dropped    _          = refl
▷f-assoc (atten _)  present    _          = refl
▷f-assoc (atten _)  (atten _)  falsified  = refl
▷f-assoc (atten _)  (atten _)  dropped    = refl
▷f-assoc (atten _)  (atten _)  present    = refl
▷f-assoc (atten d)  (atten e)  (atten g)  = cong atten (⊕d-assoc d e g)
▷f-assoc (atten _)  (atten _)  predicated = refl
▷f-assoc (atten _)  predicated falsified  = refl
▷f-assoc (atten _)  predicated dropped    = refl
▷f-assoc (atten _)  predicated present    = refl
▷f-assoc (atten _)  predicated (atten _)  = refl
▷f-assoc (atten _)  predicated predicated = refl
▷f-assoc predicated falsified  _          = refl
▷f-assoc predicated dropped    _          = refl
▷f-assoc predicated present    _          = refl
▷f-assoc predicated (atten _)  falsified  = refl
▷f-assoc predicated (atten _)  dropped    = refl
▷f-assoc predicated (atten _)  present    = refl
▷f-assoc predicated (atten _)  (atten _)  = refl
▷f-assoc predicated (atten _)  predicated = refl
▷f-assoc predicated predicated falsified  = refl
▷f-assoc predicated predicated dropped    = refl
▷f-assoc predicated predicated present    = refl
▷f-assoc predicated predicated (atten _)  = refl
▷f-assoc predicated predicated predicated = refl

▷f-unitL : ∀ f → present ▷f f ≡ f
▷f-unitL _ = refl

▷f-unitR : ∀ f → f ▷f present ≡ f
▷f-unitR present      = refl
▷f-unitR (atten _)    = refl
▷f-unitR predicated   = refl
▷f-unitR dropped      = refl
▷f-unitR falsified    = refl

-- L5 (fate): falsified (deceptive bottom) is left-absorbing — a lie composed
-- with anything is the same lie; it cannot be cancelled back out.
falsified-absorbL : ∀ f → falsified ▷f f ≡ falsified
falsified-absorbL _ = refl

-- dropped is ALSO left-absorbing — but it is honest withholding, not deception.
dropped-absorbL : ∀ f → dropped ▷f f ≡ dropped
dropped-absorbL _ = refl

-- F3 (fate): conicality. The only factoring of the unit is unit ▷ unit.
▷f-conical : ∀ a b → a ▷f b ≡ present → (a ≡ present) × (b ≡ present)
▷f-conical present    b          h  = refl , h
▷f-conical (atten _)  present    ()
▷f-conical (atten _)  (atten _)  ()
▷f-conical (atten _)  predicated ()
▷f-conical (atten _)  dropped    ()
▷f-conical (atten _)  falsified  ()
▷f-conical dropped    _          ()
▷f-conical falsified  _          ()
▷f-conical predicated present    ()
▷f-conical predicated (atten _)  ()
▷f-conical predicated predicated ()
▷f-conical predicated dropped    ()
▷f-conical predicated falsified  ()

--------------------------------------------------------------------------------
-- Coordinate 2 — bond  (Coords.idr / GradeBoundary.lean Bond.comp)
-- Commutative meet on the chain intact ⊐ withheld ⊐ severed, misbound absorbing.
--------------------------------------------------------------------------------

data Bond : Set where
  intact   : Bond
  withheld : Bond
  severed  : Bond
  misbound : Bond

infixl 7 _▷b_
_▷b_ : Bond → Bond → Bond
intact   ▷b b        = b
withheld ▷b intact   = withheld
withheld ▷b withheld = withheld
withheld ▷b severed  = severed
withheld ▷b misbound = misbound
severed  ▷b intact   = severed
severed  ▷b withheld = severed
severed  ▷b severed  = severed
severed  ▷b misbound = misbound
misbound ▷b _        = misbound

▷b-assoc : ∀ a b c → a ▷b (b ▷b c) ≡ (a ▷b b) ▷b c
▷b-assoc intact   _        _        = refl
▷b-assoc withheld intact   _        = refl
▷b-assoc withheld withheld intact   = refl
▷b-assoc withheld withheld withheld = refl
▷b-assoc withheld withheld severed  = refl
▷b-assoc withheld withheld misbound = refl
▷b-assoc withheld severed  intact   = refl
▷b-assoc withheld severed  withheld = refl
▷b-assoc withheld severed  severed  = refl
▷b-assoc withheld severed  misbound = refl
▷b-assoc withheld misbound _        = refl
▷b-assoc severed  intact   _        = refl
▷b-assoc severed  withheld intact   = refl
▷b-assoc severed  withheld withheld = refl
▷b-assoc severed  withheld severed  = refl
▷b-assoc severed  withheld misbound = refl
▷b-assoc severed  severed  intact   = refl
▷b-assoc severed  severed  withheld = refl
▷b-assoc severed  severed  severed  = refl
▷b-assoc severed  severed  misbound = refl
▷b-assoc severed  misbound _        = refl
▷b-assoc misbound _        _        = refl

▷b-unitL : ∀ b → intact ▷b b ≡ b
▷b-unitL _ = refl

▷b-unitR : ∀ b → b ▷b intact ≡ b
▷b-unitR intact   = refl
▷b-unitR withheld = refl
▷b-unitR severed  = refl
▷b-unitR misbound = refl

-- L5 (bond): misbound (deceptive bottom) is left-absorbing.
misbound-absorbL : ∀ b → misbound ▷b b ≡ misbound
misbound-absorbL _ = refl

▷b-conical : ∀ a b → a ▷b b ≡ intact → (a ≡ intact) × (b ≡ intact)
▷b-conical intact   b        h = refl , h
▷b-conical withheld intact   ()
▷b-conical withheld withheld ()
▷b-conical withheld severed  ()
▷b-conical withheld misbound ()
▷b-conical severed  intact   ()
▷b-conical severed  withheld ()
▷b-conical severed  severed  ()
▷b-conical severed  misbound ()
▷b-conical misbound _        ()

--------------------------------------------------------------------------------
-- Coordinate 3 — merge  (Coords.idr / GradeBoundary.lean Merge.comp)
-- Commutative meet on single ⊐ fused ⊐ conflated, conflated absorbing.
--------------------------------------------------------------------------------

data Merge : Set where
  single    : Merge
  fused     : Merge
  conflated : Merge

infixl 7 _▷m_
_▷m_ : Merge → Merge → Merge
single    ▷m m        = m
fused     ▷m single   = fused
fused     ▷m fused    = fused
fused     ▷m conflated = conflated
conflated ▷m _        = conflated

▷m-assoc : ∀ a b c → a ▷m (b ▷m c) ≡ (a ▷m b) ▷m c
▷m-assoc single    _         _         = refl
▷m-assoc fused     single    _         = refl
▷m-assoc fused     fused     single    = refl
▷m-assoc fused     fused     fused     = refl
▷m-assoc fused     fused     conflated = refl
▷m-assoc fused     conflated _         = refl
▷m-assoc conflated _         _         = refl

▷m-unitL : ∀ m → single ▷m m ≡ m
▷m-unitL _ = refl

▷m-unitR : ∀ m → m ▷m single ≡ m
▷m-unitR single    = refl
▷m-unitR fused     = refl
▷m-unitR conflated = refl

-- L5 (merge): conflated (deceptive bottom) is left-absorbing.
conflated-absorbL : ∀ m → conflated ▷m m ≡ conflated
conflated-absorbL _ = refl

▷m-conical : ∀ a b → a ▷m b ≡ single → (a ≡ single) × (b ≡ single)
▷m-conical single    b         h = refl , h
▷m-conical fused     single    ()
▷m-conical fused     fused     ()
▷m-conical fused     conflated ()
▷m-conical conflated _         ()

--------------------------------------------------------------------------------
-- The grade  (Grade.idr §3 / GradeBoundary.lean Grade)
-- flat record Fate⁴ × Bond × Merge, fully INDEPENDENT fields, gcomp pointwise.
--------------------------------------------------------------------------------

record Grade : Set where
  constructor mkGrade
  field
    fQuality : Fate
    fBearer  : Fate
    fContext : Fate
    fRecord  : Fate
    gBond    : Bond
    gMerge   : Merge
open Grade public

-- The unit grade ε: full presence everywhere, intact, single.
ε : Grade
ε = mkGrade present present present present intact single

infixl 5 _▷_
_▷_ : Grade → Grade → Grade
mkGrade q₁ b₁ c₁ r₁ bo₁ m₁ ▷ mkGrade q₂ b₂ c₂ r₂ bo₂ m₂ =
  mkGrade (q₁ ▷f q₂) (b₁ ▷f b₂) (c₁ ▷f c₂) (r₁ ▷f r₂) (bo₁ ▷b bo₂) (m₁ ▷m m₂)

--------------------------------------------------------------------------------
-- F1 — Grade is a Monoid (componentwise). DEGENERATE-TO-PRODUCT, constructive.
--------------------------------------------------------------------------------

gmonoid-assoc : ∀ a b c → a ▷ (b ▷ c) ≡ (a ▷ b) ▷ c
gmonoid-assoc (mkGrade q₁ b₁ c₁ r₁ bo₁ m₁) (mkGrade q₂ b₂ c₂ r₂ bo₂ m₂) (mkGrade q₃ b₃ c₃ r₃ bo₃ m₃)
  rewrite ▷f-assoc q₁ q₂ q₃ | ▷f-assoc b₁ b₂ b₃ | ▷f-assoc c₁ c₂ c₃
        | ▷f-assoc r₁ r₂ r₃ | ▷b-assoc bo₁ bo₂ bo₃ | ▷m-assoc m₁ m₂ m₃ = refl

gmonoid-unitL : ∀ g → ε ▷ g ≡ g
gmonoid-unitL (mkGrade q b c r bo m) = refl

gmonoid-unitR : ∀ g → g ▷ ε ≡ g
gmonoid-unitR (mkGrade q b c r bo m)
  rewrite ▷f-unitR q | ▷f-unitR b | ▷f-unitR c | ▷f-unitR r
        | ▷b-unitR bo | ▷m-unitR m = refl

--------------------------------------------------------------------------------
-- F2 — the product is NON-COMMUTATIVE (MANDATORY, must not be modelled as
-- commutative). Witnessed at Fate's two disagreeing absorbing heads, lifted to
-- the fQuality field. This is grade_mul_not_comm of the Lean.
--------------------------------------------------------------------------------

-- The witnessing pair: dropped ▷ falsified = dropped, falsified ▷ dropped = falsified.
gA gB : Grade
gA = mkGrade dropped   present present present intact single
gB = mkGrade falsified present present present intact single

dropped≢falsified : ¬ (dropped ≡ falsified)
dropped≢falsified ()

grade-not-comm : ¬ (∀ a b → a ▷ b ≡ b ▷ a)
grade-not-comm comm = dropped≢falsified (cong fQuality (comm gA gB))

--------------------------------------------------------------------------------
-- F3 — conicality on the full carrier:  a ▷ b ≡ ε → a ≡ ε ∧ b ≡ ε.
--------------------------------------------------------------------------------

grade-conical : ∀ a b → a ▷ b ≡ ε → (a ≡ ε) × (b ≡ ε)
grade-conical (mkGrade q₁ b₁ c₁ r₁ bo₁ m₁) (mkGrade q₂ b₂ c₂ r₂ bo₂ m₂) h
  with cong fQuality h | cong fBearer h | cong fContext h
     | cong fRecord h  | cong gBond h   | cong gMerge h
... | hq | hb | hc | hr | hbo | hm
  with ▷f-conical q₁ q₂ hq | ▷f-conical b₁ b₂ hb | ▷f-conical c₁ c₂ hc
     | ▷f-conical r₁ r₂ hr | ▷b-conical bo₁ bo₂ hbo | ▷m-conical m₁ m₂ hm
... | (eq₁ , eq₂) | (eb₁ , eb₂) | (ec₁ , ec₂) | (er₁ , er₂) | (ebo₁ , ebo₂) | (em₁ , em₂)
  rewrite eq₁ | eb₁ | ec₁ | er₁ | ebo₁ | em₁
        | eq₂ | eb₂ | ec₂ | er₂ | ebo₂ | em₂ = refl , refl
