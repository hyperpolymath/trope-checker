-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
||| The fidelity dimension of the field-fate coordinate: δ ∈ ℕ ∪ {∞, ⊤}.
||| Finite δ is tropical (min-plus) quantified loss; ∞ (`Total`) is total
||| quantified loss; ⊤ (`Unknown`) is loss of UNKNOWN amount — the honest answer
||| for unbounded recursion (calculus §3.1, §7). Composition adds loss tropically
||| with ⊤ absorbing ∞ absorbing finite (calculus L3).
module Trope.Fidelity

import Data.Nat
import Decidable.Equality

%default total

public export
data Delta : Type where
  ||| finite quantified loss; `Q 0` = no fidelity loss
  Q : Nat -> Delta
  ||| total quantified loss (∞)
  Total : Delta
  ||| unknown amount (⊤): the absorbing bottom of fidelity
  Unknown : Delta

||| Tropical addition of loss (calculus §4.1, L3): ⊤ absorbs ∞ absorbs finite.
||| Fully explicit clauses so the proofs below reduce by computation.
public export
dplus : Delta -> Delta -> Delta
dplus (Q a)    (Q b)    = Q (a + b)
dplus (Q a)    Total    = Total
dplus (Q a)    Unknown  = Unknown
dplus Total    (Q b)    = Total
dplus Total    Total    = Total
dplus Total    Unknown  = Unknown
dplus Unknown  _        = Unknown

||| L1 for the fidelity dimension: tropical addition is associative.
||| Only finite/finite/finite needs Nat associativity; absorbing cases are Refl.
export
dplusAssoc : (a, b, c : Delta) -> dplus a (dplus b c) = dplus (dplus a b) c
dplusAssoc (Q x)   (Q y)   (Q z)   = cong Q (plusAssociative x y z)
dplusAssoc (Q x)   (Q y)   Total   = Refl
dplusAssoc (Q x)   (Q y)   Unknown = Refl
dplusAssoc (Q x)   Total   (Q z)   = Refl
dplusAssoc (Q x)   Total   Total   = Refl
dplusAssoc (Q x)   Total   Unknown = Refl
dplusAssoc (Q x)   Unknown (Q z)   = Refl
dplusAssoc (Q x)   Unknown Total   = Refl
dplusAssoc (Q x)   Unknown Unknown = Refl
dplusAssoc Total   (Q y)   (Q z)   = Refl
dplusAssoc Total   (Q y)   Total   = Refl
dplusAssoc Total   (Q y)   Unknown = Refl
dplusAssoc Total   Total   (Q z)   = Refl
dplusAssoc Total   Total   Total   = Refl
dplusAssoc Total   Total   Unknown = Refl
dplusAssoc Total   Unknown (Q z)   = Refl
dplusAssoc Total   Unknown Total   = Refl
dplusAssoc Total   Unknown Unknown = Refl
dplusAssoc Unknown _       _       = Refl

||| `Q 0` is the right unit of tropical addition.
export
dplusZeroR : (a : Delta) -> dplus a (Q 0) = a
dplusZeroR (Q a)    = cong Q (plusZeroRightNeutral a)
dplusZeroR Total    = Refl
dplusZeroR Unknown  = Refl

public export
DecEq Delta where
  decEq (Q a) (Q b) = case decEq a b of
    Yes prf   => Yes (cong Q prf)
    No contra => No (\Refl => contra Refl)
  decEq (Q _) Total    = No (\Refl impossible)
  decEq (Q _) Unknown  = No (\Refl impossible)
  decEq Total (Q _)    = No (\Refl impossible)
  decEq Total Total    = Yes Refl
  decEq Total Unknown  = No (\Refl impossible)
  decEq Unknown (Q _)  = No (\Refl impossible)
  decEq Unknown Total  = No (\Refl impossible)
  decEq Unknown Unknown = Yes Refl

||| Fidelity RETENTION order as a decidable Boolean: `dLte x y` is true iff y
||| retains at least as much fidelity as x. Retention DECREASES as loss grows:
||| Q 0 (top) ⊐ Q 1 ⊐ ... ⊐ Total ⊐ Unknown (bottom).
public export
dLte : Delta -> Delta -> Bool
dLte Unknown _        = True            -- ⊤ is the bottom: ⊤ ⊑ everything
dLte (Q a)   (Q b)    = lte b a         -- y=Q b retains ≥ x=Q a  iff  b ≤ a
dLte (Q a)   Total    = False           -- a finite loss is not ⊑ total loss
dLte (Q a)   Unknown  = False           -- nothing finite is ⊑ ⊤
dLte Total   (Q b)    = True            -- total loss ⊑ any finite loss
dLte Total   Total    = True
dLte Total   Unknown  = False

||| `lte` on Nat is reflexive (Boolean form).
lteReflB : (n : Nat) -> lte n n = True
lteReflB Z     = Refl
lteReflB (S k) = lteReflB k

||| The fidelity retention order is reflexive.
export
dLteRefl : (a : Delta) -> dLte a a = True
dLteRefl (Q a)    = lteReflB a
dLteRefl Total    = Refl
dLteRefl Unknown  = Refl
