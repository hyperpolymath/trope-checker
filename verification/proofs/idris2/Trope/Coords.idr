-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
||| The three loss-shape coordinates (calculus §3): field-fate, bond, merge.
||| Each carries its composition ▷, its retention order ⊑, decidable equality,
||| and the unit (L2) + associativity (L1) laws — totality-checked with no axioms.
|||
||| Each coordinate has exactly one DECEPTIVE inhabitant (Falsified for fate,
||| Misbound for bond, Conflated for merge): the BOTTOM of its order (worst
||| retention) and absorbing under ▷ — TWO-SIDEDLY on fate since R-2026-07-07 (A1)
||| — so a deceptive grade fails every honest floor and never composes away
||| (calculus §3.3, HC-2). Provenance tags on Fused are erased here
||| (they are metadata; they do not affect the lattice laws) — the executable
||| checker (src/checker) carries them.
module Trope.Coords

import Data.Nat
import Decidable.Equality
import Trope.Fidelity

%default total


--------------------------------------------------------------------------------
-- Coordinate 1: field fate (calculus §3.1, as amended by R-2026-07-07 (A2)).
-- A CHAIN: Falsified ⊏ Dropped ⊏ Predicated ⊏ Atten(Unknown) ⊏ … ⊏ Atten(Q 0)
-- ⊏ Present. The duck check survives in the form that matters: Predicated stays
-- strictly below every Atten, so a floor of Atten δ still rejects the checkbox
-- AND the dropped field; what R-2026-07-07 (A2) adds is only Dropped ⊑ Predicated
-- (a checkbox retains at least as much as nothing at all). Atten carries the
-- fidelity δ; Falsified is the deceptive dual (false value).
--------------------------------------------------------------------------------
public export
data Fate : Type where
  ||| the field survives faithfully (lattice top)
  Present : Fate
  ||| survives, fidelity degraded by δ (Atten (Q 0) is faithful in retention)
  Atten : Delta -> Fate
  ||| quality survives only as the value of a predicate — the checkbox
  Predicated : Fate
  ||| withheld entirely
  Dropped : Fate
  ||| deceptive dual: a value asserted faithful that is in fact false
  Falsified : Fate

||| Fate composition ▷ (calculus §4.1, as amended by R-2026-07-07 (A1)).
||| Falsified is a TWO-SIDED zero: it absorbs from the left, and — per
||| R-2026-07-07 (A1) — an upstream Dropped no longer erases a downstream lie
||| (Dropped ▷ Falsified = Falsified), so no composition order launders
||| deception (L5 strengthened). Dropped absorbs every other right operand;
||| Present is the unit; Atten ▷ Atten adds loss tropically; collapse
||| (Predicated) subsumes prior fidelity loss. With (A1) composition is
||| commutative and ⊑-monotone in both arguments (Trope.Soundness.fateL4Mono*).
||| Clauses are fully explicit (bar the left-absorbing Falsified head) so the
||| laws below reduce by computation.
public export
fateCompose : Fate -> Fate -> Fate
fateCompose Falsified  _          = Falsified
fateCompose Dropped    Falsified  = Falsified   -- R-2026-07-07 (A1): the lie survives the drop
fateCompose Dropped    Present    = Dropped
fateCompose Dropped    (Atten _)  = Dropped
fateCompose Dropped    Predicated = Dropped
fateCompose Dropped    Dropped    = Dropped
fateCompose Present    f          = f
fateCompose (Atten d1) Falsified  = Falsified
fateCompose (Atten d1) Dropped    = Dropped
fateCompose (Atten d1) Present    = Atten d1
fateCompose (Atten d1) (Atten d2) = Atten (dplus d1 d2)
fateCompose (Atten d1) Predicated = Predicated
fateCompose Predicated Falsified  = Falsified
fateCompose Predicated Dropped    = Dropped
fateCompose Predicated Present    = Predicated
fateCompose Predicated (Atten _)  = Predicated
fateCompose Predicated Predicated = Predicated

||| Fate retention order ⊑ (calculus §3.1, as amended by R-2026-07-07 (A2)):
||| a CHAIN — Present top; Atten segment ordered by δ; Predicated below every
||| Atten; Dropped below Predicated (A2: a checkbox retains at least as much as
||| nothing at all — the converse stays False, so a floor of Predicated still
||| rejects Dropped); Falsified the bottom (worst), so every honest floor fails
||| against it.
public export
fateLte : Fate -> Fate -> Bool
fateLte Falsified _          = True
fateLte _          Falsified = False
fateLte _          Present    = True
fateLte Present    _          = False
fateLte (Atten a)  (Atten b)  = dLte a b
fateLte (Atten _)  Predicated = False
fateLte (Atten _)  Dropped    = False
fateLte Predicated (Atten _)  = True
fateLte Predicated Predicated = True
fateLte Predicated Dropped    = False
fateLte Dropped    (Atten _)  = True
fateLte Dropped    Predicated = True    -- R-2026-07-07 (A2): a checkbox ⊒ nothing
fateLte Dropped    Dropped    = True

public export
DecEq Fate where
  decEq Present Present = Yes Refl
  decEq (Atten a) (Atten b) = case decEq a b of
    Yes prf => Yes (cong Atten prf)
    No contra => No (\Refl => contra Refl)
  decEq Predicated Predicated = Yes Refl
  decEq Dropped Dropped = Yes Refl
  decEq Falsified Falsified = Yes Refl
  decEq Present (Atten _) = No (\Refl impossible)
  decEq Present Predicated = No (\Refl impossible)
  decEq Present Dropped = No (\Refl impossible)
  decEq Present Falsified = No (\Refl impossible)
  decEq (Atten _) Present = No (\Refl impossible)
  decEq (Atten _) Predicated = No (\Refl impossible)
  decEq (Atten _) Dropped = No (\Refl impossible)
  decEq (Atten _) Falsified = No (\Refl impossible)
  decEq Predicated Present = No (\Refl impossible)
  decEq Predicated (Atten _) = No (\Refl impossible)
  decEq Predicated Dropped = No (\Refl impossible)
  decEq Predicated Falsified = No (\Refl impossible)
  decEq Dropped Present = No (\Refl impossible)
  decEq Dropped (Atten _) = No (\Refl impossible)
  decEq Dropped Predicated = No (\Refl impossible)
  decEq Dropped Falsified = No (\Refl impossible)
  decEq Falsified Present = No (\Refl impossible)
  decEq Falsified (Atten _) = No (\Refl impossible)
  decEq Falsified Predicated = No (\Refl impossible)
  decEq Falsified Dropped = No (\Refl impossible)

||| L2: Present is the unit of fate composition.
export
fateUnitL : (f : Fate) -> fateCompose Present f = f
fateUnitL f = Refl

export
fateUnitR : (f : Fate) -> fateCompose f Present = f
fateUnitR Present    = Refl
fateUnitR (Atten d)  = Refl
fateUnitR Predicated = Refl
fateUnitR Dropped    = Refl
fateUnitR Falsified  = Refl

export
fateLteRefl : (f : Fate) -> fateLte f f = True
fateLteRefl Present    = Refl
fateLteRefl (Atten a)  = dLteRefl a
fateLteRefl Predicated = Refl
fateLteRefl Dropped    = Refl
fateLteRefl Falsified  = Refl

||| L1: fate composition is associative — including through the R-2026-07-07 (A1)
||| clause (Dropped ▷ Falsified = Falsified). Left-absorbing heads (Falsified,
||| Present) close in one clause each; Dropped heads split on the tail since
||| Dropped ▷ Falsified now differs from Dropped ▷ (honest); the all-Atten case
||| needs dplusAssoc; the rest reduce by computation.
export
fateAssoc : (a, b, c : Fate) -> fateCompose a (fateCompose b c) = fateCompose (fateCompose a b) c
fateAssoc Falsified b c = Refl
fateAssoc Dropped Falsified c = Refl
fateAssoc Dropped Present c = Refl
fateAssoc Dropped (Atten d2) Falsified = Refl
fateAssoc Dropped (Atten d2) Present = Refl
fateAssoc Dropped (Atten d2) (Atten d3) = Refl
fateAssoc Dropped (Atten d2) Predicated = Refl
fateAssoc Dropped (Atten d2) Dropped = Refl
fateAssoc Dropped Predicated Falsified = Refl
fateAssoc Dropped Predicated Present = Refl
fateAssoc Dropped Predicated (Atten d3) = Refl
fateAssoc Dropped Predicated Predicated = Refl
fateAssoc Dropped Predicated Dropped = Refl
fateAssoc Dropped Dropped Falsified = Refl
fateAssoc Dropped Dropped Present = Refl
fateAssoc Dropped Dropped (Atten d3) = Refl
fateAssoc Dropped Dropped Predicated = Refl
fateAssoc Dropped Dropped Dropped = Refl
fateAssoc Present b c = Refl
fateAssoc (Atten d1) Falsified c = Refl
fateAssoc (Atten d1) Dropped Falsified = Refl
fateAssoc (Atten d1) Dropped Present = Refl
fateAssoc (Atten d1) Dropped (Atten d3) = Refl
fateAssoc (Atten d1) Dropped Predicated = Refl
fateAssoc (Atten d1) Dropped Dropped = Refl
fateAssoc (Atten d1) Present c = Refl
fateAssoc (Atten d1) (Atten d2) Present = Refl
fateAssoc (Atten d1) (Atten d2) Falsified = Refl
fateAssoc (Atten d1) (Atten d2) Dropped = Refl
fateAssoc (Atten d1) (Atten d2) (Atten d3) = cong Atten (dplusAssoc d1 d2 d3)
fateAssoc (Atten d1) (Atten d2) Predicated = Refl
fateAssoc (Atten d1) Predicated Present = Refl
fateAssoc (Atten d1) Predicated Falsified = Refl
fateAssoc (Atten d1) Predicated Dropped = Refl
fateAssoc (Atten d1) Predicated (Atten d3) = Refl
fateAssoc (Atten d1) Predicated Predicated = Refl
fateAssoc Predicated Falsified c = Refl
fateAssoc Predicated Dropped Falsified = Refl
fateAssoc Predicated Dropped Present = Refl
fateAssoc Predicated Dropped (Atten d3) = Refl
fateAssoc Predicated Dropped Predicated = Refl
fateAssoc Predicated Dropped Dropped = Refl
fateAssoc Predicated Present c = Refl
fateAssoc Predicated (Atten d2) Present = Refl
fateAssoc Predicated (Atten d2) Falsified = Refl
fateAssoc Predicated (Atten d2) Dropped = Refl
fateAssoc Predicated (Atten d2) (Atten d3) = Refl
fateAssoc Predicated (Atten d2) Predicated = Refl
fateAssoc Predicated Predicated Present = Refl
fateAssoc Predicated Predicated Falsified = Refl
fateAssoc Predicated Predicated Dropped = Refl
fateAssoc Predicated Predicated (Atten d3) = Refl
fateAssoc Predicated Predicated Predicated = Refl

public export
data Bond : Type where
  Intact : Bond
  Withheld : Bond
  Severed : Bond
  Misbound : Bond   -- deceptive: the bottom (worst retention), absorbing under the meet

||| Composition ▷ on Bond: honest meet on the chain (Intact ⊐ Withheld ⊐ Severed),
||| with Misbound (deceptive) absorbing (calculus §4.1, L3/L5).
public export
bondCompose : Bond -> Bond -> Bond
bondCompose Intact Intact = Intact
bondCompose Intact Withheld = Withheld
bondCompose Intact Severed = Severed
bondCompose Intact Misbound = Misbound
bondCompose Withheld Intact = Withheld
bondCompose Withheld Withheld = Withheld
bondCompose Withheld Severed = Severed
bondCompose Withheld Misbound = Misbound
bondCompose Severed Intact = Severed
bondCompose Severed Withheld = Severed
bondCompose Severed Severed = Severed
bondCompose Severed Misbound = Misbound
bondCompose Misbound Intact = Misbound
bondCompose Misbound Withheld = Misbound
bondCompose Misbound Severed = Misbound
bondCompose Misbound Misbound = Misbound

||| Retention order ⊑ on Bond (decidable Boolean): x ⊑ y iff y retains ≥ x.
public export
bondLte : Bond -> Bond -> Bool
bondLte Intact Intact = True
bondLte Intact Withheld = False
bondLte Intact Severed = False
bondLte Intact Misbound = False
bondLte Withheld Intact = True
bondLte Withheld Withheld = True
bondLte Withheld Severed = False
bondLte Withheld Misbound = False
bondLte Severed Intact = True
bondLte Severed Withheld = True
bondLte Severed Severed = True
bondLte Severed Misbound = False
bondLte Misbound Intact = True
bondLte Misbound Withheld = True
bondLte Misbound Severed = True
bondLte Misbound Misbound = True

public export
DecEq Bond where
  decEq Intact Intact = Yes Refl
  decEq Intact Withheld = No (\Refl impossible)
  decEq Intact Severed = No (\Refl impossible)
  decEq Intact Misbound = No (\Refl impossible)
  decEq Withheld Intact = No (\Refl impossible)
  decEq Withheld Withheld = Yes Refl
  decEq Withheld Severed = No (\Refl impossible)
  decEq Withheld Misbound = No (\Refl impossible)
  decEq Severed Intact = No (\Refl impossible)
  decEq Severed Withheld = No (\Refl impossible)
  decEq Severed Severed = Yes Refl
  decEq Severed Misbound = No (\Refl impossible)
  decEq Misbound Intact = No (\Refl impossible)
  decEq Misbound Withheld = No (\Refl impossible)
  decEq Misbound Severed = No (\Refl impossible)
  decEq Misbound Misbound = Yes Refl

||| L2: Intact (the chain top) is the unit of ▷ on Bond.
export
bondUnitL : (x : Bond) -> bondCompose Intact x = x
bondUnitL Intact = Refl
bondUnitL Withheld = Refl
bondUnitL Severed = Refl
bondUnitL Misbound = Refl
export
bondUnitR : (x : Bond) -> bondCompose x Intact = x
bondUnitR Intact = Refl
bondUnitR Withheld = Refl
bondUnitR Severed = Refl
bondUnitR Misbound = Refl

export
bondLteRefl : (x : Bond) -> bondLte x x = True
bondLteRefl Intact = Refl
bondLteRefl Withheld = Refl
bondLteRefl Severed = Refl
bondLteRefl Misbound = Refl

||| L1: ▷ is associative on Bond (exhaustive; honest meet + absorbing deceptive).
export
bondAssoc : (x, y, z : Bond) -> bondCompose x (bondCompose y z) = bondCompose (bondCompose x y) z
bondAssoc Intact Intact Intact = Refl
bondAssoc Intact Intact Withheld = Refl
bondAssoc Intact Intact Severed = Refl
bondAssoc Intact Intact Misbound = Refl
bondAssoc Intact Withheld Intact = Refl
bondAssoc Intact Withheld Withheld = Refl
bondAssoc Intact Withheld Severed = Refl
bondAssoc Intact Withheld Misbound = Refl
bondAssoc Intact Severed Intact = Refl
bondAssoc Intact Severed Withheld = Refl
bondAssoc Intact Severed Severed = Refl
bondAssoc Intact Severed Misbound = Refl
bondAssoc Intact Misbound Intact = Refl
bondAssoc Intact Misbound Withheld = Refl
bondAssoc Intact Misbound Severed = Refl
bondAssoc Intact Misbound Misbound = Refl
bondAssoc Withheld Intact Intact = Refl
bondAssoc Withheld Intact Withheld = Refl
bondAssoc Withheld Intact Severed = Refl
bondAssoc Withheld Intact Misbound = Refl
bondAssoc Withheld Withheld Intact = Refl
bondAssoc Withheld Withheld Withheld = Refl
bondAssoc Withheld Withheld Severed = Refl
bondAssoc Withheld Withheld Misbound = Refl
bondAssoc Withheld Severed Intact = Refl
bondAssoc Withheld Severed Withheld = Refl
bondAssoc Withheld Severed Severed = Refl
bondAssoc Withheld Severed Misbound = Refl
bondAssoc Withheld Misbound Intact = Refl
bondAssoc Withheld Misbound Withheld = Refl
bondAssoc Withheld Misbound Severed = Refl
bondAssoc Withheld Misbound Misbound = Refl
bondAssoc Severed Intact Intact = Refl
bondAssoc Severed Intact Withheld = Refl
bondAssoc Severed Intact Severed = Refl
bondAssoc Severed Intact Misbound = Refl
bondAssoc Severed Withheld Intact = Refl
bondAssoc Severed Withheld Withheld = Refl
bondAssoc Severed Withheld Severed = Refl
bondAssoc Severed Withheld Misbound = Refl
bondAssoc Severed Severed Intact = Refl
bondAssoc Severed Severed Withheld = Refl
bondAssoc Severed Severed Severed = Refl
bondAssoc Severed Severed Misbound = Refl
bondAssoc Severed Misbound Intact = Refl
bondAssoc Severed Misbound Withheld = Refl
bondAssoc Severed Misbound Severed = Refl
bondAssoc Severed Misbound Misbound = Refl
bondAssoc Misbound Intact Intact = Refl
bondAssoc Misbound Intact Withheld = Refl
bondAssoc Misbound Intact Severed = Refl
bondAssoc Misbound Intact Misbound = Refl
bondAssoc Misbound Withheld Intact = Refl
bondAssoc Misbound Withheld Withheld = Refl
bondAssoc Misbound Withheld Severed = Refl
bondAssoc Misbound Withheld Misbound = Refl
bondAssoc Misbound Severed Intact = Refl
bondAssoc Misbound Severed Withheld = Refl
bondAssoc Misbound Severed Severed = Refl
bondAssoc Misbound Severed Misbound = Refl
bondAssoc Misbound Misbound Intact = Refl
bondAssoc Misbound Misbound Withheld = Refl
bondAssoc Misbound Misbound Severed = Refl
bondAssoc Misbound Misbound Misbound = Refl

public export
data Merge : Type where
  Single : Merge
  Fused : Merge
  Conflated : Merge   -- deceptive: the bottom (worst retention), absorbing under the meet

||| Composition ▷ on Merge: honest meet on the chain (Single ⊐ Fused),
||| with Conflated (deceptive) absorbing (calculus §4.1, L3/L5).
public export
mergeCompose : Merge -> Merge -> Merge
mergeCompose Single Single = Single
mergeCompose Single Fused = Fused
mergeCompose Single Conflated = Conflated
mergeCompose Fused Single = Fused
mergeCompose Fused Fused = Fused
mergeCompose Fused Conflated = Conflated
mergeCompose Conflated Single = Conflated
mergeCompose Conflated Fused = Conflated
mergeCompose Conflated Conflated = Conflated

||| Retention order ⊑ on Merge (decidable Boolean): x ⊑ y iff y retains ≥ x.
public export
mergeLte : Merge -> Merge -> Bool
mergeLte Single Single = True
mergeLte Single Fused = False
mergeLte Single Conflated = False
mergeLte Fused Single = True
mergeLte Fused Fused = True
mergeLte Fused Conflated = False
mergeLte Conflated Single = True
mergeLte Conflated Fused = True
mergeLte Conflated Conflated = True

public export
DecEq Merge where
  decEq Single Single = Yes Refl
  decEq Single Fused = No (\Refl impossible)
  decEq Single Conflated = No (\Refl impossible)
  decEq Fused Single = No (\Refl impossible)
  decEq Fused Fused = Yes Refl
  decEq Fused Conflated = No (\Refl impossible)
  decEq Conflated Single = No (\Refl impossible)
  decEq Conflated Fused = No (\Refl impossible)
  decEq Conflated Conflated = Yes Refl

||| L2: Single (the chain top) is the unit of ▷ on Merge.
export
mergeUnitL : (x : Merge) -> mergeCompose Single x = x
mergeUnitL Single = Refl
mergeUnitL Fused = Refl
mergeUnitL Conflated = Refl
export
mergeUnitR : (x : Merge) -> mergeCompose x Single = x
mergeUnitR Single = Refl
mergeUnitR Fused = Refl
mergeUnitR Conflated = Refl

export
mergeLteRefl : (x : Merge) -> mergeLte x x = True
mergeLteRefl Single = Refl
mergeLteRefl Fused = Refl
mergeLteRefl Conflated = Refl

||| L1: ▷ is associative on Merge (exhaustive; honest meet + absorbing deceptive).
export
mergeAssoc : (x, y, z : Merge) -> mergeCompose x (mergeCompose y z) = mergeCompose (mergeCompose x y) z
mergeAssoc Single Single Single = Refl
mergeAssoc Single Single Fused = Refl
mergeAssoc Single Single Conflated = Refl
mergeAssoc Single Fused Single = Refl
mergeAssoc Single Fused Fused = Refl
mergeAssoc Single Fused Conflated = Refl
mergeAssoc Single Conflated Single = Refl
mergeAssoc Single Conflated Fused = Refl
mergeAssoc Single Conflated Conflated = Refl
mergeAssoc Fused Single Single = Refl
mergeAssoc Fused Single Fused = Refl
mergeAssoc Fused Single Conflated = Refl
mergeAssoc Fused Fused Single = Refl
mergeAssoc Fused Fused Fused = Refl
mergeAssoc Fused Fused Conflated = Refl
mergeAssoc Fused Conflated Single = Refl
mergeAssoc Fused Conflated Fused = Refl
mergeAssoc Fused Conflated Conflated = Refl
mergeAssoc Conflated Single Single = Refl
mergeAssoc Conflated Single Fused = Refl
mergeAssoc Conflated Single Conflated = Refl
mergeAssoc Conflated Fused Single = Refl
mergeAssoc Conflated Fused Fused = Refl
mergeAssoc Conflated Fused Conflated = Refl
mergeAssoc Conflated Conflated Single = Refl
mergeAssoc Conflated Conflated Fused = Refl
mergeAssoc Conflated Conflated Conflated = Refl
