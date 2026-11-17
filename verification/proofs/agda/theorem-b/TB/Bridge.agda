{-# OPTIONS --safe --without-K --cubical-compatible --exact-split #-}
-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
--
-- Theorem B — the definition bridge for the Rocq and Lean recheck legs of the
-- ratified-carrier order laws and L4 (PROOF-POLICY §2.2).
--
-- A re-proved leg restates the Agda definitions by hand, and a restated
-- definition can drift from its source while every theorem about it still
-- proves. This module pins the values of the six definitions the legs restate
-- (fateLte, _▷f_, bondLte, _▷b_, mergeLte, _▷m_) on a fixed sample, as lists
-- of numerals. verification/proofs/rocq/RatifiedOrder.v and
-- verification/proofs/lean4/ratified-order/RatifiedOrder.lean state the SAME
-- six literals about their own restatements and prove them by computation.
-- If any one restatement disagrees with the Agda at any sample point, that
-- prover's kernel rejects its bridge theorem.
--
-- Coverage: Bond (4 × 4) and Merge (3 × 3) are covered exhaustively. Fate is
-- covered on nine points, top to bottom: present, atten (Q 0), atten (Q 2),
-- atten (Q 5), atten total, atten unknown, predicated, dropped, falsified
-- (81 pairs); the Atten pairs exercise Δ addition (Q 2 ⊕d Q 5 = Q 7).
-- The fateLte table is lower-triangular in that order: the chain, visibly.
--
-- Codes: Fate present 0, atten (Q n) 10 + n, atten total 1, atten unknown 2,
-- predicated 3, dropped 4, falsified 5; Bond intact 0, withheld 1, severed 2,
-- misbound 3; Merge single 0, fused 1, conflated 2; a Boolean is 1 or 0.

module TB.Bridge where

open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base using (List; []; _∷_; map; concatMap)
open import Data.Nat.Base using (ℕ; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import TB.Grade
open import TB.Order

b2n : Bool → ℕ
b2n true  = 1
b2n false = 0

fcode : Fate → ℕ
fcode present         = 0
fcode (atten (Q n))   = 10 + n
fcode (atten total)   = 1
fcode (atten unknown) = 2
fcode predicated      = 3
fcode dropped         = 4
fcode falsified       = 5

bcode : Bond → ℕ
bcode intact   = 0
bcode withheld = 1
bcode severed  = 2
bcode misbound = 3

mcode : Merge → ℕ
mcode single    = 0
mcode fused     = 1
mcode conflated = 2

sampleF : List Fate
sampleF = present ∷ atten (Q 0) ∷ atten (Q 2) ∷ atten (Q 5) ∷ atten total
        ∷ atten unknown ∷ predicated ∷ dropped ∷ falsified ∷ []

sampleB : List Bond
sampleB = intact ∷ withheld ∷ severed ∷ misbound ∷ []

sampleM : List Merge
sampleM = single ∷ fused ∷ conflated ∷ []

-- Every ordered pair of the sample, row by row: tbl f [x₁ … xₙ] =
-- f x₁ x₁ … f x₁ xₙ, f x₂ x₁ …
tbl : {A : Set} → (A → A → ℕ) → List A → List ℕ
tbl f xs = concatMap (λ x → map (f x) xs) xs

fateLteTable-literal : List ℕ
fateLteTable-literal =
    1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷
    0 ∷ 1 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷
    0 ∷ 0 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷
    0 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷
    1 ∷ 1 ∷ 1 ∷ 0 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ []

fcompTable-literal : List ℕ
fcompTable-literal =
    0 ∷ 10 ∷ 12 ∷ 15 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 10 ∷ 10 ∷ 12 ∷ 15 ∷ 1 ∷ 2 ∷
    3 ∷ 4 ∷ 5 ∷ 12 ∷ 12 ∷ 14 ∷ 17 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 15 ∷ 15 ∷ 17 ∷
    20 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 2 ∷
    2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 3 ∷ 3 ∷ 3 ∷ 3 ∷ 3 ∷ 3 ∷ 3 ∷ 4 ∷ 5 ∷
    4 ∷ 4 ∷ 4 ∷ 4 ∷ 4 ∷ 4 ∷ 4 ∷ 4 ∷ 5 ∷ 5 ∷ 5 ∷ 5 ∷ 5 ∷ 5 ∷ 5 ∷ 5 ∷ 5 ∷
    5 ∷ []

bondLteTable-literal : List ℕ
bondLteTable-literal =
    1 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 1 ∷ 0 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ []

bcompTable-literal : List ℕ
bcompTable-literal =
    0 ∷ 1 ∷ 2 ∷ 3 ∷ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 2 ∷ 2 ∷ 2 ∷ 3 ∷ 3 ∷ 3 ∷ 3 ∷ 3 ∷ []

mergeLteTable-literal : List ℕ
mergeLteTable-literal =
    1 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ 1 ∷ 1 ∷ 1 ∷ []

mcompTable-literal : List ℕ
mcompTable-literal =
    0 ∷ 1 ∷ 2 ∷ 1 ∷ 1 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ []

bridge-fateLte : tbl (λ x y → b2n (fateLte x y)) sampleF ≡ fateLteTable-literal
bridge-fateLte = refl

bridge-fcomp : tbl (λ x y → fcode (x ▷f y)) sampleF ≡ fcompTable-literal
bridge-fcomp = refl

bridge-bondLte : tbl (λ x y → b2n (bondLte x y)) sampleB ≡ bondLteTable-literal
bridge-bondLte = refl

bridge-bcomp : tbl (λ x y → bcode (x ▷b y)) sampleB ≡ bcompTable-literal
bridge-bcomp = refl

bridge-mergeLte : tbl (λ x y → b2n (mergeLte x y)) sampleM ≡ mergeLteTable-literal
bridge-mergeLte = refl

bridge-mcomp : tbl (λ x y → mcode (x ▷m y)) sampleM ≡ mcompTable-literal
bridge-mcomp = refl
