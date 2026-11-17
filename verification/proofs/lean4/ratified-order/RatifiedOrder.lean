/-
SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
SPDX-License-Identifier: MPL-2.0

Lean recheck leg, route re-proved, for the ratified-carrier order laws and
L4 (monotonicity) in full. Source of truth: the Agda modules
verification/proofs/agda/theorem-b/TB/{Grade,Order,OrderLaws,Monotone}.agda.

Only Lean core is used: no `import`, no Mathlib (PROOF-POLICY §2). Unlike the
grade-boundary and grade-factorisation packages, which import Mathlib and stay
BRIDGE-PENDING, this file is meant to count as a recheck leg.

Every Agda definition used is restated with the same constructors and clauses,
and every theorem with the same hypotheses and conclusion; each is proved
again by hand. No `simp`, `omega`, `decide` or `ac_rfl`: proofs are `cases`,
`rfl`, `rw`, `nomatch` and term application, so that no theorem depends on an axiom
(`#print axioms` at the foot of this file; CI audits every theorem).

Encoding differences, all of them notation:
- Agda's ℕ, Bool, _∧_ and _≡_ are Nat, Bool, `&&` and `=`. Lean's `&&` is
  left-associative and Agda's `_∧_` right-associative, so every conjunction
  below is parenthesised right-nested, as in the Agda.
- Agda's `_⊎_` is `Or`: both disjuncts are propositions here.
- Agda's infix operators are named functions: `_⊕d_` is `dplus`, `_▷f_`
  `fcomp`, `_▷b_` `bcomp`, `_▷m_` `mcomp`, `_▷_` `gcomp`, `_⊑_` `gle`.
  Hyphens become underscores.
- `IsTotalOrder` is unfolded into its four laws (reflexive, transitive,
  antisymmetric, total), which is what the standard-library record carries.
-/

namespace TropeRatified

/-! ## The carrier (TB.Grade) -/

inductive Delta where
  | Q (n : Nat)
  | total
  | unknown

open Delta

def dplus : Delta → Delta → Delta
  | unknown, _       => unknown
  | total,   unknown => unknown
  | total,   total   => total
  | total,   Q _     => total
  | Q _,     unknown => unknown
  | Q _,     total   => total
  | Q a,     Q b     => Q (a + b)

inductive Fate where
  | present
  | atten (d : Delta)
  | predicated
  | dropped
  | falsified

open Fate

def fcomp : Fate → Fate → Fate
  | falsified,  _          => falsified
  | dropped,    falsified  => falsified
  | dropped,    present    => dropped
  | dropped,    atten _    => dropped
  | dropped,    predicated => dropped
  | dropped,    dropped    => dropped
  | present,    f          => f
  | atten _,    falsified  => falsified
  | atten _,    dropped    => dropped
  | atten d,    present    => atten d
  | atten d,    atten e    => atten (dplus d e)
  | atten _,    predicated => predicated
  | predicated, falsified  => falsified
  | predicated, dropped    => dropped
  | predicated, present    => predicated
  | predicated, atten _    => predicated
  | predicated, predicated => predicated

inductive Bond where
  | intact
  | withheld
  | severed
  | misbound

open Bond

def bcomp : Bond → Bond → Bond
  | intact,   b        => b
  | withheld, intact   => withheld
  | withheld, withheld => withheld
  | withheld, severed  => severed
  | withheld, misbound => misbound
  | severed,  intact   => severed
  | severed,  withheld => severed
  | severed,  severed  => severed
  | severed,  misbound => misbound
  | misbound, _        => misbound

inductive Merge where
  | single
  | fused
  | conflated

open Merge

def mcomp : Merge → Merge → Merge
  | single,    m         => m
  | fused,     single    => fused
  | fused,     fused     => fused
  | fused,     conflated => conflated
  | conflated, _         => conflated

structure Grade where
  mkGrade ::
  fQuality : Fate
  fBearer  : Fate
  fContext : Fate
  fRecord  : Fate
  gBond    : Bond
  gMerge   : Merge

def gcomp (g h : Grade) : Grade :=
  ⟨fcomp g.fQuality h.fQuality, fcomp g.fBearer h.fBearer,
   fcomp g.fContext h.fContext, fcomp g.fRecord h.fRecord,
   bcomp g.gBond h.gBond, mcomp g.gMerge h.gMerge⟩

/-! ## The retention order (TB.Order) -/

def lteb : Nat → Nat → Bool
  | 0,     _     => true
  | _ + 1, 0     => false
  | m + 1, n + 1 => lteb m n

def dLte : Delta → Delta → Bool
  | unknown, _       => true
  | Q a,     Q b     => lteb b a
  | Q _,     total   => false
  | Q _,     unknown => false
  | total,   Q _     => true
  | total,   total   => true
  | total,   unknown => false

def fateLte : Fate → Fate → Bool
  | falsified,  _          => true
  | present,    present    => true
  | present,    atten _    => false
  | present,    predicated => false
  | present,    dropped    => false
  | present,    falsified  => false
  | atten _,    present    => true
  | atten a,    atten b    => dLte a b
  | atten _,    predicated => false
  | atten _,    dropped    => false
  | atten _,    falsified  => false
  | predicated, present    => true
  | predicated, atten _    => true
  | predicated, predicated => true
  | predicated, dropped    => false
  | predicated, falsified  => false
  | dropped,    present    => true
  | dropped,    atten _    => true
  | dropped,    predicated => true
  | dropped,    dropped    => true
  | dropped,    falsified  => false

def bondLte : Bond → Bond → Bool
  | intact,   intact   => true
  | intact,   withheld => false
  | intact,   severed  => false
  | intact,   misbound => false
  | withheld, intact   => true
  | withheld, withheld => true
  | withheld, severed  => false
  | withheld, misbound => false
  | severed,  intact   => true
  | severed,  withheld => true
  | severed,  severed  => true
  | severed,  misbound => false
  | misbound, _        => true

def mergeLte : Merge → Merge → Bool
  | single,    single    => true
  | single,    fused     => false
  | single,    conflated => false
  | fused,     single    => true
  | fused,     fused     => true
  | fused,     conflated => false
  | conflated, _         => true

def gradeLte (g h : Grade) : Bool :=
  fateLte g.fQuality h.fQuality && (fateLte g.fBearer h.fBearer &&
  (fateLte g.fContext h.fContext && (fateLte g.fRecord h.fRecord &&
  (bondLte g.gBond h.gBond && mergeLte g.gMerge h.gMerge))))

def gle (g h : Grade) : Prop := gradeLte g h = true

/-! ## Reflexivity (TB.Order) -/

theorem lteb_refl : ∀ n, lteb n n = true
  | 0     => rfl
  | n + 1 => lteb_refl n

theorem dLte_refl : ∀ d, dLte d d = true
  | Q n     => lteb_refl n
  | total   => rfl
  | unknown => rfl

theorem fateLte_refl : ∀ f, fateLte f f = true
  | present    => rfl
  | atten d    => dLte_refl d
  | predicated => rfl
  | dropped    => rfl
  | falsified  => rfl

theorem bondLte_refl : ∀ b, bondLte b b = true := by
  intro b; cases b <;> rfl

theorem mergeLte_refl : ∀ m, mergeLte m m = true := by
  intro m; cases m <;> rfl

/-! ## Six-way conjunctions, taken apart and put back -/

theorem and6_elim : ∀ a b c d e f : Bool,
    (a && (b && (c && (d && (e && f))))) = true →
    a = true ∧ b = true ∧ c = true ∧ d = true ∧ e = true ∧ f = true
  | true,  true,  true,  true,  true,  _, p => ⟨rfl, rfl, rfl, rfl, rfl, p⟩
  | true,  true,  true,  true,  false, _, p => nomatch p
  | true,  true,  true,  false, _,     _, p => nomatch p
  | true,  true,  false, _,     _,     _, p => nomatch p
  | true,  false, _,     _,     _,     _, p => nomatch p
  | false, _,     _,     _,     _,     _, p => nomatch p

theorem and6_intro : ∀ a b c d e f : Bool,
    a = true → b = true → c = true → d = true → e = true → f = true →
    (a && (b && (c && (d && (e && f))))) = true
  | _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl => rfl

theorem gle_refl (g : Grade) : gle g g :=
  and6_intro _ _ _ _ _ _ (fateLte_refl _) (fateLte_refl _) (fateLte_refl _)
    (fateLte_refl _) (bondLte_refl _) (mergeLte_refl _)

/-! ## A2-directions (TB.Order) -/

theorem fateDroppedLtePredicated : fateLte dropped predicated = true := rfl

theorem fatePredicatedNotLteDropped : fateLte predicated dropped = false := rfl

/-! ## Order laws (TB.OrderLaws): lteb, dLte and fateLte are chains -/

theorem lteb_trans : ∀ a b c, lteb a b = true → lteb b c = true → lteb a c = true
  | 0,     _,     _,     _, _ => rfl
  | _ + 1, 0,     _,     p, _ => nomatch p
  | _ + 1, _ + 1, 0,     _, q => nomatch q
  | a + 1, b + 1, c + 1, p, q => lteb_trans a b c p q

theorem lteb_antisym : ∀ a b, lteb a b = true → lteb b a = true → a = b
  | 0,     0,     _, _ => rfl
  | 0,     _ + 1, _, q => nomatch q
  | _ + 1, 0,     p, _ => nomatch p
  | a + 1, b + 1, p, q => congrArg (· + 1) (lteb_antisym a b p q)

theorem lteb_total : ∀ a b, lteb a b = true ∨ lteb b a = true
  | 0,     _     => Or.inl rfl
  | _ + 1, 0     => Or.inr rfl
  | a + 1, b + 1 => lteb_total a b

theorem dLte_trans : ∀ a b c, dLte a b = true → dLte b c = true → dLte a c = true := by
  intro a b c p q
  cases a <;> cases b <;> cases c <;>
    first | rfl | (cases p; done) | (cases q; done)
          | exact lteb_trans _ _ _ q p

theorem dLte_antisym : ∀ a b, dLte a b = true → dLte b a = true → a = b := by
  intro a b p q
  cases a <;> cases b <;>
    first | rfl | (cases p; done) | (cases q; done)
          | exact congrArg Delta.Q (lteb_antisym _ _ q p)

theorem dLte_total : ∀ a b, dLte a b = true ∨ dLte b a = true := by
  intro a b
  cases a <;> cases b <;>
    first | exact Or.inl rfl | exact Or.inr rfl | exact lteb_total _ _

theorem fateLte_trans : ∀ x y z,
    fateLte x y = true → fateLte y z = true → fateLte x z = true := by
  intro x y z p q
  cases x <;> cases y <;> cases z <;>
    first | rfl | (cases p; done) | (cases q; done)
          | exact dLte_trans _ _ _ p q

theorem fateLte_antisym : ∀ x y,
    fateLte x y = true → fateLte y x = true → x = y := by
  intro x y p q
  cases x <;> cases y <;>
    first | rfl | (cases p; done) | (cases q; done)
          | exact congrArg Fate.atten (dLte_antisym _ _ p q)

theorem fateLte_total : ∀ x y, fateLte x y = true ∨ fateLte y x = true := by
  intro x y
  cases x <;> cases y <;>
    first | exact Or.inl rfl | exact Or.inr rfl | exact dLte_total _ _

/-- A2-chain as one statement: the four laws of a total order. -/
theorem fate_isTotalOrder :
    (∀ x, fateLte x x = true) ∧
    (∀ x y z, fateLte x y = true → fateLte y z = true → fateLte x z = true) ∧
    (∀ x y, fateLte x y = true → fateLte y x = true → x = y) ∧
    (∀ x y, fateLte x y = true ∨ fateLte y x = true) :=
  ⟨fateLte_refl, fateLte_trans, fateLte_antisym, fateLte_total⟩

theorem dLte_isTotalOrder :
    (∀ a, dLte a a = true) ∧
    (∀ a b c, dLte a b = true → dLte b c = true → dLte a c = true) ∧
    (∀ a b, dLte a b = true → dLte b a = true → a = b) ∧
    (∀ a b, dLte a b = true ∨ dLte b a = true) :=
  ⟨dLte_refl, dLte_trans, dLte_antisym, dLte_total⟩

theorem bondLte_trans : ∀ x y z,
    bondLte x y = true → bondLte y z = true → bondLte x z = true := by
  intro x y z p q
  cases x <;> cases y <;> cases z <;>
    first | rfl | (cases p; done) | (cases q; done)

theorem mergeLte_trans : ∀ x y z,
    mergeLte x y = true → mergeLte y z = true → mergeLte x z = true := by
  intro x y z p q
  cases x <;> cases y <;> cases z <;>
    first | rfl | (cases p; done) | (cases q; done)

/-! ## retention-order (TB.OrderLaws): ⊑ is a decidable preorder -/

theorem gle_trans : ∀ g h k, gle g h → gle h k → gle g k := by
  intro g h k p q
  have ⟨pq, pb, pc, pr, pbo, pm⟩ := and6_elim _ _ _ _ _ _ p
  have ⟨qq, qb, qc, qr, qbo, qm⟩ := and6_elim _ _ _ _ _ _ q
  exact and6_intro _ _ _ _ _ _
    (fateLte_trans _ _ _ pq qq) (fateLte_trans _ _ _ pb qb)
    (fateLte_trans _ _ _ pc qc) (fateLte_trans _ _ _ pr qr)
    (bondLte_trans _ _ _ pbo qbo) (mergeLte_trans _ _ _ pm qm)

/-- ⊑ is decided by its own Boolean (Agda `⊑-dec`). -/
def gle_dec (g h : Grade) : Decidable (gle g h) :=
  match hb : gradeLte g h with
  | true  => isTrue hb
  | false => isFalse (fun p => nomatch hb.symm.trans p)

/-- The decision procedure is sound and complete for ⊑, as a theorem the
axiom audit inspects. -/
theorem gle_decides (g h : Grade) : gle g h ∨ ¬ gle g h :=
  match hb : gradeLte g h with
  | true  => Or.inl hb
  | false => Or.inr (fun p => nomatch hb.symm.trans p)

/-! ## L4-fidelity (TB.Order): dplus is monotone in each argument -/

theorem lteb_suc_right : ∀ a b, lteb a b = true → lteb a (b + 1) = true
  | 0,     _,     _ => rfl
  | _ + 1, 0,     p => nomatch p
  | a + 1, b + 1, p => lteb_suc_right a b p

theorem lteb_self_plus : ∀ m n, lteb m (m + n) = true
  | 0,     n => by rw [Nat.zero_add]; rfl
  | m + 1, n => by rw [Nat.succ_add]; exact lteb_self_plus m n

theorem lteb_plus_left : ∀ m n, lteb n (m + n) = true
  | 0,     n => by rw [Nat.zero_add]; exact lteb_refl n
  | m + 1, n => by rw [Nat.succ_add]; exact lteb_suc_right n (m + n) (lteb_plus_left m n)

theorem lteb_plus_monoL : ∀ c a b, lteb a b = true → lteb (c + a) (c + b) = true
  | 0,     a, b, p => by rw [Nat.zero_add, Nat.zero_add]; exact p
  | c + 1, a, b, p => by rw [Nat.succ_add, Nat.succ_add]; exact lteb_plus_monoL c a b p

theorem lteb_plus_monoR : ∀ a b c, lteb a b = true → lteb (a + c) (b + c) = true
  | 0,     b,     c, _ => by rw [Nat.zero_add]; exact lteb_plus_left b c
  | _ + 1, 0,     _, p => nomatch p
  | a + 1, b + 1, c, p => by
      rw [Nat.succ_add, Nat.succ_add]; exact lteb_plus_monoR a b c p

theorem dplusMonoR : ∀ c a b, dLte a b = true → dLte (dplus c a) (dplus c b) = true := by
  intro c a b p
  cases c <;> cases a <;> cases b <;>
    first | rfl | (cases p; done) | exact lteb_plus_monoL _ _ _ p

theorem dplusMonoL : ∀ a b c, dLte a b = true → dLte (dplus a c) (dplus b c) = true := by
  intro a b c p
  cases a <;> cases b <;> cases c <;>
    first | rfl | (cases p; done) | exact lteb_plus_monoR _ _ _ p

theorem dplusRetLteR : ∀ d a, dLte (dplus d a) d = true := by
  intro d a
  cases d <;> cases a <;> first | rfl | exact lteb_self_plus _ _

theorem dplusRetLteL : ∀ a e, dLte (dplus a e) e = true := by
  intro a e
  cases a <;> cases e <;> first | rfl | exact lteb_plus_left _ _

/-! ## L4-fate (TB.Order) -/

theorem fateL4MonoR : ∀ h x y,
    fateLte x y = true → fateLte (fcomp h x) (fcomp h y) = true := by
  intro h x y p
  cases h <;> cases x <;> cases y <;>
    first | rfl | exact p | (cases p; done) | exact dLte_refl _
          | exact dplusRetLteR _ _ | exact dplusMonoR _ _ _ p

theorem fateL4MonoL : ∀ x y h,
    fateLte x y = true → fateLte (fcomp x h) (fcomp y h) = true := by
  intro x y h p
  cases x <;> cases y <;> cases h <;>
    first | rfl | exact p | (cases p; done) | exact dLte_refl _
          | exact dplusRetLteL _ _ | exact dplusMonoL _ _ _ p

/-! ## L4-bond-merge (TB.Monotone) -/

theorem bondL4MonoR : ∀ h x y,
    bondLte x y = true → bondLte (bcomp h x) (bcomp h y) = true := by
  intro h x y p
  cases h <;> cases x <;> cases y <;> first | rfl | (cases p; done)

theorem bondL4MonoL : ∀ x y h,
    bondLte x y = true → bondLte (bcomp x h) (bcomp y h) = true := by
  intro x y h p
  cases x <;> cases y <;> cases h <;> first | rfl | (cases p; done)

theorem mergeL4MonoR : ∀ h x y,
    mergeLte x y = true → mergeLte (mcomp h x) (mcomp h y) = true := by
  intro h x y p
  cases h <;> cases x <;> cases y <;> first | rfl | (cases p; done)

theorem mergeL4MonoL : ∀ x y h,
    mergeLte x y = true → mergeLte (mcomp x h) (mcomp y h) = true := by
  intro x y h p
  cases x <;> cases y <;> cases h <;> first | rfl | (cases p; done)

/-! ## L4-lifting (TB.Monotone): gcomp is ⊑-monotone -/

theorem gradeL4MonoR : ∀ k g h, gle g h → gle (gcomp k g) (gcomp k h) := by
  intro k g h p
  have ⟨pq, pb, pc, pr, pbo, pm⟩ := and6_elim _ _ _ _ _ _ p
  exact and6_intro _ _ _ _ _ _
    (fateL4MonoR _ _ _ pq) (fateL4MonoR _ _ _ pb)
    (fateL4MonoR _ _ _ pc) (fateL4MonoR _ _ _ pr)
    (bondL4MonoR _ _ _ pbo) (mergeL4MonoR _ _ _ pm)

theorem gradeL4MonoL : ∀ g h k, gle g h → gle (gcomp g k) (gcomp h k) := by
  intro g h k p
  have ⟨pq, pb, pc, pr, pbo, pm⟩ := and6_elim _ _ _ _ _ _ p
  exact and6_intro _ _ _ _ _ _
    (fateL4MonoL _ _ _ pq) (fateL4MonoL _ _ _ pb)
    (fateL4MonoL _ _ _ pc) (fateL4MonoL _ _ _ pr)
    (bondL4MonoL _ _ _ pbo) (mergeL4MonoL _ _ _ pm)

/-- Both arguments at once (Agda `▷-mono`). -/
theorem gcomp_mono : ∀ g₁ g₂ h₁ h₂,
    gle g₁ g₂ → gle h₁ h₂ → gle (gcomp g₁ h₁) (gcomp g₂ h₂) :=
  fun g₁ g₂ h₁ h₂ p q =>
    gle_trans _ _ _ (gradeL4MonoL g₁ g₂ h₁ p) (gradeL4MonoR g₂ h₁ h₂ q)

/-! ## Definition bridge (TB.Bridge)

The same six literals as the Agda and the Rocq: if this file's restatement of
any of the six definitions disagrees with the Agda at a sample point, the
matching bridge theorem fails. Bond and Merge are covered exhaustively; Fate
on nine points, top to bottom. Codes as in TB/Bridge.agda. -/

def b2n : Bool → Nat
  | true  => 1
  | false => 0

def fcode : Fate → Nat
  | present         => 0
  | atten (Q n)     => 10 + n
  | atten total     => 1
  | atten unknown   => 2
  | predicated      => 3
  | dropped         => 4
  | falsified       => 5

def bcode : Bond → Nat
  | intact   => 0
  | withheld => 1
  | severed  => 2
  | misbound => 3

def mcode : Merge → Nat
  | single    => 0
  | fused     => 1
  | conflated => 2

def sampleF : List Fate :=
  [present, atten (Q 0), atten (Q 2), atten (Q 5), atten total,
   atten unknown, predicated, dropped, falsified]

def sampleB : List Bond := [intact, withheld, severed, misbound]

def sampleM : List Merge := [single, fused, conflated]

def lmap {α β : Type} (f : α → β) : List α → List β
  | []     => []
  | x :: t => f x :: lmap f t

def lappend {α : Type} : List α → List α → List α
  | [],     ys => ys
  | x :: t, ys => x :: lappend t ys

def lconcatMap {α β : Type} (f : α → List β) : List α → List β
  | []     => []
  | x :: t => lappend (f x) (lconcatMap f t)

def tbl {α : Type} (f : α → α → Nat) (xs : List α) : List Nat :=
  lconcatMap (fun x => lmap (f x) xs) xs

def fateLteTable_literal : List Nat :=
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0,
   0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1,
   1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1,
   1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1]

def fcompTable_literal : List Nat :=
  [0, 10, 12, 15, 1, 2, 3, 4, 5, 10, 10, 12, 15, 1, 2, 3, 4, 5, 12, 12,
   14, 17, 1, 2, 3, 4, 5, 15, 15, 17, 20, 1, 2, 3, 4, 5, 1, 1, 1, 1, 1,
   2, 3, 4, 5, 2, 2, 2, 2, 2, 2, 3, 4, 5, 3, 3, 3, 3, 3, 3, 3, 4, 5, 4,
   4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5]

def bondLteTable_literal : List Nat :=
  [1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1]

def bcompTable_literal : List Nat :=
  [0, 1, 2, 3, 1, 1, 2, 3, 2, 2, 2, 3, 3, 3, 3, 3]

def mergeLteTable_literal : List Nat :=
  [1, 0, 0, 1, 1, 0, 1, 1, 1]

def mcompTable_literal : List Nat :=
  [0, 1, 2, 1, 1, 2, 2, 2, 2]

theorem bridge_fateLte : tbl (fun x y => b2n (fateLte x y)) sampleF = fateLteTable_literal := rfl

theorem bridge_fcomp : tbl (fun x y => fcode (fcomp x y)) sampleF = fcompTable_literal := rfl

theorem bridge_bondLte : tbl (fun x y => b2n (bondLte x y)) sampleB = bondLteTable_literal := rfl

theorem bridge_bcomp : tbl (fun x y => bcode (bcomp x y)) sampleB = bcompTable_literal := rfl

theorem bridge_mergeLte : tbl (fun x y => b2n (mergeLte x y)) sampleM = mergeLteTable_literal := rfl

theorem bridge_mcomp : tbl (fun x y => mcode (mcomp x y)) sampleM = mcompTable_literal := rfl

end TropeRatified

/-! ## Axiom report (the CI audit re-derives this for every theorem) -/

#print axioms TropeRatified.fate_isTotalOrder
#print axioms TropeRatified.gle_trans
#print axioms TropeRatified.gle_decides
#print axioms TropeRatified.fateL4MonoR
#print axioms TropeRatified.fateL4MonoL
#print axioms TropeRatified.dplusMonoR
#print axioms TropeRatified.dplusMonoL
#print axioms TropeRatified.bondL4MonoR
#print axioms TropeRatified.bondL4MonoL
#print axioms TropeRatified.mergeL4MonoR
#print axioms TropeRatified.mergeL4MonoL
#print axioms TropeRatified.gradeL4MonoR
#print axioms TropeRatified.gradeL4MonoL
#print axioms TropeRatified.gcomp_mono
#print axioms TropeRatified.bridge_fcomp
