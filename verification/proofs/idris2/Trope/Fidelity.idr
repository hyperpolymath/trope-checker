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

-- ── Nat Boolean-lte plumbing for the dplus monotonicity lemmas ──────────────
-- (Needed by Trope.Soundness.fateL4Mono{L,R} — the L4 monotonicity restored by
-- R-2026-07-07 (A1)/(A2) — for the Atten/Atten cases.)

||| Boolean lte is preserved by a successor on the right.
lteSuccRightB : (a, b : Nat) -> lte a b = True -> lte a (S b) = True
lteSuccRightB Z     _     _   = Refl
lteSuccRightB (S k) Z     prf = absurd prf
lteSuccRightB (S k) (S j) prf = lteSuccRightB k j prf

||| `m ≤ m + n` (Boolean lte), by induction on m.
lteBSelfPlus : (m, n : Nat) -> lte m (m + n) = True
lteBSelfPlus Z     n = Refl
lteBSelfPlus (S k) n = lteBSelfPlus k n

||| `n ≤ m + n` (Boolean lte), by induction on m.
lteBPlusLeft : (m, n : Nat) -> lte n (m + n) = True
lteBPlusLeft Z     n = lteReflB n
lteBPlusLeft (S k) n = lteSuccRightB n (k + n) (lteBPlusLeft k n)

||| Boolean lte is monotone under addition of a constant on the LEFT.
ltePlusMonoLeft : (c, a, b : Nat) -> lte a b = True -> lte (c + a) (c + b) = True
ltePlusMonoLeft Z     a b prf = prf
ltePlusMonoLeft (S k) a b prf = ltePlusMonoLeft k a b prf

||| Boolean lte is monotone under addition of a constant on the RIGHT.
ltePlusMonoRight : (a, b, c : Nat) -> lte a b = True -> lte (a + c) (b + c) = True
ltePlusMonoRight Z     b     c _   = lteBPlusLeft b c
ltePlusMonoRight (S x) Z     c prf = absurd prf
ltePlusMonoRight (S x) (S y) c prf = ltePlusMonoRight x y c prf

-- ── dplus is ⊑-monotone (retention) in each argument, and adding loss on
-- either side can only lower retention. These are the Delta facts behind fate
-- L4 monotonicity (Trope.Soundness, R-2026-07-07). ─────────────────────────

||| Left-composition monotonicity: dLte a b → dLte (c + a) (c + b).
export
dplusMonoR : (c, a, b : Delta) -> dLte a b = True -> dLte (dplus c a) (dplus c b) = True
dplusMonoR Unknown a     b     _   = Refl
dplusMonoR (Q m)   (Q x) (Q y) prf = ltePlusMonoLeft m y x prf
dplusMonoR (Q m)   (Q x) Total prf = absurd prf
dplusMonoR (Q m)   (Q x) Unknown prf = absurd prf
dplusMonoR (Q m)   Total (Q y) _   = Refl
dplusMonoR (Q m)   Total Total _   = Refl
dplusMonoR (Q m)   Total Unknown prf = absurd prf
dplusMonoR (Q m)   Unknown (Q y) _ = Refl
dplusMonoR (Q m)   Unknown Total _ = Refl
dplusMonoR (Q m)   Unknown Unknown _ = Refl
dplusMonoR Total   (Q x) (Q y) _   = Refl
dplusMonoR Total   (Q x) Total prf = absurd prf
dplusMonoR Total   (Q x) Unknown prf = absurd prf
dplusMonoR Total   Total (Q y) _   = Refl
dplusMonoR Total   Total Total _   = Refl
dplusMonoR Total   Total Unknown prf = absurd prf
dplusMonoR Total   Unknown (Q y) _ = Refl
dplusMonoR Total   Unknown Total _ = Refl
dplusMonoR Total   Unknown Unknown _ = Refl

||| Right-composition monotonicity: dLte a b → dLte (a + c) (b + c).
export
dplusMonoL : (a, b, c : Delta) -> dLte a b = True -> dLte (dplus a c) (dplus b c) = True
dplusMonoL Unknown b     c       _   = Refl
dplusMonoL (Q x)   (Q y) (Q n)   prf = ltePlusMonoRight y x n prf
dplusMonoL (Q x)   (Q y) Total   _   = Refl
dplusMonoL (Q x)   (Q y) Unknown _   = Refl
dplusMonoL (Q x)   Total c       prf = absurd prf
dplusMonoL (Q x)   Unknown c     prf = absurd prf
dplusMonoL Total   (Q y) (Q n)   _   = Refl
dplusMonoL Total   (Q y) Total   _   = Refl
dplusMonoL Total   (Q y) Unknown _   = Refl
dplusMonoL Total   Total (Q n)   _   = Refl
dplusMonoL Total   Total Total   _   = Refl
dplusMonoL Total   Total Unknown _   = Refl
dplusMonoL Total   Unknown c     prf = absurd prf

||| Adding loss on the RIGHT can only lower retention: dplus d a ⊑ d.
export
dplusRetLteR : (d, a : Delta) -> dLte (dplus d a) d = True
dplusRetLteR (Q m)   (Q n)   = lteBSelfPlus m n
dplusRetLteR (Q m)   Total   = Refl
dplusRetLteR (Q m)   Unknown = Refl
dplusRetLteR Total   (Q n)   = Refl
dplusRetLteR Total   Total   = Refl
dplusRetLteR Total   Unknown = Refl
dplusRetLteR Unknown a       = Refl

||| Adding loss on the LEFT can only lower retention: dplus a e ⊑ e.
export
dplusRetLteL : (a, e : Delta) -> dLte (dplus a e) e = True
dplusRetLteL (Q m)   (Q n)   = lteBPlusLeft m n
dplusRetLteL (Q m)   Total   = Refl
dplusRetLteL (Q m)   Unknown = Refl
dplusRetLteL Total   (Q n)   = Refl
dplusRetLteL Total   Total   = Refl
dplusRetLteL Total   Unknown = Refl
dplusRetLteL Unknown e       = Refl
