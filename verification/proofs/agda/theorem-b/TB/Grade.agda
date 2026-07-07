{-# OPTIONS --safe --without-K #-}
-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
--
-- Theorem B, Target 1 — the trope-particularity grade algebra as a graded
-- structure, in Agda, --safe --without-K. MIGRATED to the RATIFIED carrier
-- (amendments R-2026-07-07 (A1)/(A2), docs/decisions/0004-ratified-carrier-
-- amendments.adoc).
--
-- This module mirrors the ratified carrier clause-for-clause from the Idris2
-- ground truth (verification/proofs/idris2/Trope/{Fidelity,Coords}.idr, as
-- migrated by ADR 0004) and the Lean amendment probe
-- (verification/proofs/lean4/grade-boundary/L4Monotonicity.lean, FateA).
-- The original Lean frozen interface (GradeBoundary.lean) describes the
-- PRE-RATIFICATION carrier and is retained upstream under a provenance note.
--
--   F1  Grade is a product Monoid (componentwise)           — gmonoid-{assoc,unitL,unitR}
--   F2′ the product is COMMUTATIVE on the ratified carrier   — grade-comm
--       (HISTORICAL: F2 "non-commutative" — grade-not-comm, mirroring the
--        Lean grade_mul_not_comm — was a theorem of the PRE-ratification
--        carrier only. Its sole witness was the clause Dropped ▷ Falsified
--        = Dropped, amended away by R-2026-07-07 (A1): each deceptive bottom
--        is now a TWO-SIDED zero, so no composition order launders deception.)
--   F3  conicality on the full carrier                       — grade-conical
--   F4  three-tier strict boundary                           — §F4 below (SURVIVES the
--       amendments: deceptive (two-sided zeros ⇒ non-cancellative, L5),
--       honest-but-lossy (still non-cancellative), cancellative core
--       (finite fidelity, Q embeds ℕ).
--
-- Reuses the STYLE of echo-types/proofs/agda/EchoGraded.agda (a thin-poset
-- reindexing modality: a decidable, propositional order with a degrade action)
-- — the retention order ⊑ lives in TB.Order in that exact spirit.

module TB.Grade where

open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ; +-cancelʳ-≡)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; sym; trans)

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

-- dplus is commutative (tropical addition; the tops absorb symmetrically).
⊕d-comm : ∀ a b → a ⊕d b ≡ b ⊕d a
⊕d-comm (Q a)   (Q b)   = cong Q (+-comm a b)
⊕d-comm (Q _)   total   = refl
⊕d-comm (Q _)   unknown = refl
⊕d-comm total   (Q _)   = refl
⊕d-comm total   total   = refl
⊕d-comm total   unknown = refl
⊕d-comm unknown (Q _)   = refl
⊕d-comm unknown total   = refl
⊕d-comm unknown unknown = refl

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
-- Coordinate 1 — field fate  (Coords.idr §3.1 / L4Monotonicity.lean FateA.comp,
-- as amended by R-2026-07-07 (A1), ADR 0004).
-- A COMMUTATIVE monoid: present is the unit; falsified (deceptive bottom) is a
-- TWO-SIDED zero — per (A1) an upstream dropped no longer erases a downstream
-- lie (dropped ▷f falsified = falsified), so no composition order launders
-- deception (L5 strengthened). dropped absorbs every other right operand.
-- Clause-for-clause, exactly as the migrated Idris2 ground truth (Coords.idr).
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
dropped    ▷f falsified  = falsified   -- R-2026-07-07 (A1): the lie survives the drop
dropped    ▷f present    = dropped
dropped    ▷f atten _    = dropped
dropped    ▷f predicated = dropped
dropped    ▷f dropped    = dropped
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

-- F1 (fate): associativity — including through the R-2026-07-07 (A1) clause.
-- The dropped head now splits on the tail (dropped ▷f falsified differs from
-- dropped ▷f honest); the only non-refl clause is atten/atten/atten.
▷f-assoc : ∀ a b c → a ▷f (b ▷f c) ≡ (a ▷f b) ▷f c
▷f-assoc falsified  _          _          = refl
▷f-assoc dropped    falsified  _          = refl
▷f-assoc dropped    present    _          = refl
▷f-assoc dropped    (atten _)  falsified  = refl
▷f-assoc dropped    (atten _)  present    = refl
▷f-assoc dropped    (atten _)  (atten _)  = refl
▷f-assoc dropped    (atten _)  predicated = refl
▷f-assoc dropped    (atten _)  dropped    = refl
▷f-assoc dropped    predicated falsified  = refl
▷f-assoc dropped    predicated present    = refl
▷f-assoc dropped    predicated (atten _)  = refl
▷f-assoc dropped    predicated predicated = refl
▷f-assoc dropped    predicated dropped    = refl
▷f-assoc dropped    dropped    falsified  = refl
▷f-assoc dropped    dropped    present    = refl
▷f-assoc dropped    dropped    (atten _)  = refl
▷f-assoc dropped    dropped    predicated = refl
▷f-assoc dropped    dropped    dropped    = refl
▷f-assoc present    _          _          = refl
▷f-assoc (atten _)  falsified  _          = refl
▷f-assoc (atten _)  dropped    falsified  = refl
▷f-assoc (atten _)  dropped    present    = refl
▷f-assoc (atten _)  dropped    (atten _)  = refl
▷f-assoc (atten _)  dropped    predicated = refl
▷f-assoc (atten _)  dropped    dropped    = refl
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
▷f-assoc predicated dropped    falsified  = refl
▷f-assoc predicated dropped    present    = refl
▷f-assoc predicated dropped    (atten _)  = refl
▷f-assoc predicated dropped    predicated = refl
▷f-assoc predicated dropped    dropped    = refl
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

-- L5 (fate), STRENGTHENED by R-2026-07-07 (A1): falsified (deceptive bottom)
-- is a TWO-SIDED zero — a lie composed with anything, in either order, is the
-- same lie; no honest absorber launders it (Lean FateA.falsified_two_sided_zero).
falsified-absorbL : ∀ f → falsified ▷f f ≡ falsified
falsified-absorbL _ = refl

falsified-absorbR : ∀ f → f ▷f falsified ≡ falsified
falsified-absorbR present    = refl
falsified-absorbR (atten _)  = refl
falsified-absorbR predicated = refl
falsified-absorbR dropped    = refl
falsified-absorbR falsified  = refl

-- R-2026-07-07 (A1), pinned: the lie survives the drop.
-- (HISTORICAL: the pre-ratification carrier had dropped ▷f falsified ≡ dropped
-- — `dropped-absorbL` made dropped fully left-absorbing, the sole source of
-- non-commutativity (F2) and an L5 laundering hole. Amended away by ADR 0004.)
dropped▷falsified : dropped ▷f falsified ≡ falsified
dropped▷falsified = refl

-- dropped still absorbs every HONEST right operand — honest withholding, not
-- deception; it remains non-cancellative (tier 2 intact under the repair).
dropped-absorbs-honest : ∀ f → f ≢ falsified → dropped ▷f f ≡ dropped
dropped-absorbs-honest present    _   = refl
dropped-absorbs-honest (atten _)  _   = refl
dropped-absorbs-honest predicated _   = refl
dropped-absorbs-honest dropped    _   = refl
dropped-absorbs-honest falsified  neq = ⊥-elim (neq refl)

-- F3 (fate): conicality. The only factoring of the unit is unit ▷ unit.
▷f-conical : ∀ a b → a ▷f b ≡ present → (a ≡ present) × (b ≡ present)
▷f-conical present    b          h  = refl , h
▷f-conical (atten _)  present    ()
▷f-conical (atten _)  (atten _)  ()
▷f-conical (atten _)  predicated ()
▷f-conical (atten _)  dropped    ()
▷f-conical (atten _)  falsified  ()
▷f-conical dropped    present    ()
▷f-conical dropped    (atten _)  ()
▷f-conical dropped    predicated ()
▷f-conical dropped    dropped    ()
▷f-conical dropped    falsified  ()
▷f-conical falsified  _          ()
▷f-conical predicated present    ()
▷f-conical predicated (atten _)  ()
▷f-conical predicated predicated ()
▷f-conical predicated dropped    ()
▷f-conical predicated falsified  ()

-- COMMUTATIVITY (R-2026-07-07 (A1); mirrors Lean FateA.comp_comm): with the
-- amended clause the sole non-commuting pair (dropped, falsified) agrees.
▷f-comm : ∀ a b → a ▷f b ≡ b ▷f a
▷f-comm present    present    = refl
▷f-comm present    (atten _)  = refl
▷f-comm present    predicated = refl
▷f-comm present    dropped    = refl
▷f-comm present    falsified  = refl
▷f-comm (atten _)  present    = refl
▷f-comm (atten d)  (atten e)  = cong atten (⊕d-comm d e)
▷f-comm (atten _)  predicated = refl
▷f-comm (atten _)  dropped    = refl
▷f-comm (atten _)  falsified  = refl
▷f-comm predicated present    = refl
▷f-comm predicated (atten _)  = refl
▷f-comm predicated predicated = refl
▷f-comm predicated dropped    = refl
▷f-comm predicated falsified  = refl
▷f-comm dropped    present    = refl
▷f-comm dropped    (atten _)  = refl
▷f-comm dropped    predicated = refl
▷f-comm dropped    dropped    = refl
▷f-comm dropped    falsified  = refl   -- the (A1) clause: both sides falsified
▷f-comm falsified  present    = refl
▷f-comm falsified  (atten _)  = refl
▷f-comm falsified  predicated = refl
▷f-comm falsified  dropped    = refl
▷f-comm falsified  falsified  = refl

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

▷b-comm : ∀ a b → a ▷b b ≡ b ▷b a
▷b-comm intact   intact   = refl
▷b-comm intact   withheld = refl
▷b-comm intact   severed  = refl
▷b-comm intact   misbound = refl
▷b-comm withheld intact   = refl
▷b-comm withheld withheld = refl
▷b-comm withheld severed  = refl
▷b-comm withheld misbound = refl
▷b-comm severed  intact   = refl
▷b-comm severed  withheld = refl
▷b-comm severed  severed  = refl
▷b-comm severed  misbound = refl
▷b-comm misbound intact   = refl
▷b-comm misbound withheld = refl
▷b-comm misbound severed  = refl
▷b-comm misbound misbound = refl

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

▷m-comm : ∀ a b → a ▷m b ≡ b ▷m a
▷m-comm single    single    = refl
▷m-comm single    fused     = refl
▷m-comm single    conflated = refl
▷m-comm fused     single    = refl
▷m-comm fused     fused     = refl
▷m-comm fused     conflated = refl
▷m-comm conflated single    = refl
▷m-comm conflated fused     = refl
▷m-comm conflated conflated = refl

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
-- F2′ — the product is COMMUTATIVE on the ratified carrier (R-2026-07-07 (A1),
-- ADR 0004; mirrors Lean FateA.comp_comm lifted componentwise).
--
-- HISTORICAL NOTE: the pre-ratification carrier was NON-commutative —
-- `grade-not-comm` here (grade_mul_not_comm in GradeBoundary.lean) was PROVED,
-- witnessed by gA = ⟨dropped,…⟩, gB = ⟨falsified,…⟩ with gA ▷ gB = gA ≠ gB =
-- gB ▷ gA. That non-commutativity was an ARTIFACT of the single unamended
-- clause Dropped ▷ Falsified = Dropped (simultaneously an L5 laundering hole),
-- not intrinsic to loss-shape grading; (A1) removes it, and with it the
-- witness. grade-not-comm is a theorem of the OLD carrier only and is
-- REPLACED by the commutativity proof below.
--------------------------------------------------------------------------------

grade-comm : ∀ a b → a ▷ b ≡ b ▷ a
grade-comm (mkGrade q₁ b₁ c₁ r₁ bo₁ m₁) (mkGrade q₂ b₂ c₂ r₂ bo₂ m₂)
  rewrite ▷f-comm q₁ q₂ | ▷f-comm b₁ b₂ | ▷f-comm c₁ c₂
        | ▷f-comm r₁ r₂ | ▷b-comm bo₁ bo₂ | ▷m-comm m₁ m₂ = refl

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
