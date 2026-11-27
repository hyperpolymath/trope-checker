(* SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
   SPDX-License-Identifier: MPL-2.0

   Rocq recheck leg, route re-proved, for the ratified-carrier order laws and
   L4 (monotonicity) in full. Source of truth: the Agda modules
   verification/proofs/agda/theorem-b/TB/{Grade,Order,OrderLaws,Monotone}.agda.

   This file restates every Agda definition it uses with the same
   constructors and clauses, and states every theorem with the same
   hypotheses and conclusion; then proves each again by hand. It imports
   nothing: no standard-library module, no axiom. docs/status/PROOF-STATUS.adoc
   records the statement correspondence (PROOF-POLICY 2.2).

   Encoding differences, all of them notation:
   - Agda's ℕ is nat; Agda's Bool, true, false, _∧_ are bool, true, false,
     andb. Agda's _∧_ is infixr, so every conjunction below is written
     right-nested with explicit parentheses.
   - Agda's _≡_ is eq; Agda's _⊎_ is sumbool-free `or`, since both disjuncts
     are propositions here.
   - Agda's infix operators are named functions: _⊕d_ is dplus, _▷f_ fcomp,
     _▷b_ bcomp, _▷m_ mcomp, _▷_ gcomp, _⊑_ gle. Hyphens become underscores.
   - IsTotalOrder is unfolded into its four laws (refl, trans, antisym,
     total), which is what the standard-library record carries. *)

(* ------------------------------------------------------------------ *)
(* The carrier (TB.Grade).                                              *)
(* ------------------------------------------------------------------ *)

Inductive Delta : Set := Q (n : nat) | total | unknown.

Definition dplus (a b : Delta) : Delta :=
  match a, b with
  | unknown, _       => unknown
  | total,   unknown => unknown
  | total,   total   => total
  | total,   Q _     => total
  | Q _,     unknown => unknown
  | Q _,     total   => total
  | Q x,     Q y     => Q (x + y)
  end.

Inductive Fate : Set := present | atten (d : Delta) | predicated | dropped | falsified.

Definition fcomp (f g : Fate) : Fate :=
  match f, g with
  | falsified,  _          => falsified
  | dropped,    falsified  => falsified
  | dropped,    present    => dropped
  | dropped,    atten _    => dropped
  | dropped,    predicated => dropped
  | dropped,    dropped    => dropped
  | present,    h          => h
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
  end.

Inductive Bond : Set := intact | withheld | severed | misbound.

Definition bcomp (a b : Bond) : Bond :=
  match a, b with
  | intact,   c        => c
  | withheld, intact   => withheld
  | withheld, withheld => withheld
  | withheld, severed  => severed
  | withheld, misbound => misbound
  | severed,  intact   => severed
  | severed,  withheld => severed
  | severed,  severed  => severed
  | severed,  misbound => misbound
  | misbound, _        => misbound
  end.

Inductive Merge : Set := single | fused | conflated.

Definition mcomp (a b : Merge) : Merge :=
  match a, b with
  | single,    m         => m
  | fused,     single    => fused
  | fused,     fused     => fused
  | fused,     conflated => conflated
  | conflated, _         => conflated
  end.

Record Grade : Set := mkGrade
  { fQuality : Fate; fBearer : Fate; fContext : Fate; fRecord : Fate;
    gBond : Bond; gMerge : Merge }.

Definition gcomp (g h : Grade) : Grade :=
  mkGrade (fcomp (fQuality g) (fQuality h)) (fcomp (fBearer g) (fBearer h))
          (fcomp (fContext g) (fContext h)) (fcomp (fRecord g) (fRecord h))
          (bcomp (gBond g) (gBond h)) (mcomp (gMerge g) (gMerge h)).

(* ------------------------------------------------------------------ *)
(* The retention order (TB.Order).                                      *)
(* ------------------------------------------------------------------ *)

Fixpoint lteb (m n : nat) : bool :=
  match m, n with
  | O,   _   => true
  | S _, O   => false
  | S a, S b => lteb a b
  end.

Definition dLte (a b : Delta) : bool :=
  match a, b with
  | unknown, _       => true
  | Q x,     Q y     => lteb y x
  | Q _,     total   => false
  | Q _,     unknown => false
  | total,   Q _     => true
  | total,   total   => true
  | total,   unknown => false
  end.

Definition fateLte (f g : Fate) : bool :=
  match f, g with
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
  end.

Definition bondLte (a b : Bond) : bool :=
  match a, b with
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
  end.

Definition mergeLte (a b : Merge) : bool :=
  match a, b with
  | single,    single    => true
  | single,    fused     => false
  | single,    conflated => false
  | fused,     single    => true
  | fused,     fused     => true
  | fused,     conflated => false
  | conflated, _         => true
  end.

Definition gradeLte (g h : Grade) : bool :=
  andb (fateLte (fQuality g) (fQuality h))
  (andb (fateLte (fBearer g) (fBearer h))
  (andb (fateLte (fContext g) (fContext h))
  (andb (fateLte (fRecord g) (fRecord h))
  (andb (bondLte (gBond g) (gBond h))
        (mergeLte (gMerge g) (gMerge h)))))).

Definition gle (g h : Grade) : Prop := gradeLte g h = true.

(* ------------------------------------------------------------------ *)
(* Reflexivity (TB.Order).                                              *)
(* ------------------------------------------------------------------ *)

Lemma lteb_refl : forall n, lteb n n = true.
Proof. induction n as [|n IH]; simpl; [reflexivity | exact IH]. Qed.

Lemma dLte_refl : forall d, dLte d d = true.
Proof. intros [n| |]; simpl; [apply lteb_refl | reflexivity | reflexivity]. Qed.

Lemma fateLte_refl : forall f, fateLte f f = true.
Proof. intros [|d| | |]; simpl; try reflexivity; apply dLte_refl. Qed.

Lemma bondLte_refl : forall b, bondLte b b = true.
Proof. intros []; reflexivity. Qed.

Lemma mergeLte_refl : forall m, mergeLte m m = true.
Proof. intros []; reflexivity. Qed.

Lemma gle_refl : forall g, gle g g.
Proof.
  intros [q b c r bo m]; unfold gle, gradeLte; simpl.
  rewrite fateLte_refl, fateLte_refl, fateLte_refl, fateLte_refl,
          bondLte_refl, mergeLte_refl; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* A2-directions (TB.Order).                                            *)
(* ------------------------------------------------------------------ *)

Theorem fateDroppedLtePredicated : fateLte dropped predicated = true.
Proof. reflexivity. Qed.

Theorem fatePredicatedNotLteDropped : fateLte predicated dropped = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Order laws (TB.OrderLaws): lteb, dLte and fateLte are chains.        *)
(* ------------------------------------------------------------------ *)

Lemma lteb_trans : forall a b c, lteb a b = true -> lteb b c = true -> lteb a c = true.
Proof.
  induction a as [|a IH]; intros [|b] [|c] p q; simpl in *;
    try reflexivity; try discriminate.
  exact (IH b c p q).
Qed.

Lemma lteb_antisym : forall a b, lteb a b = true -> lteb b a = true -> a = b.
Proof.
  induction a as [|a IH]; intros [|b] p q; simpl in *;
    try reflexivity; try discriminate.
  rewrite (IH b p q); reflexivity.
Qed.

Lemma lteb_total : forall a b, lteb a b = true \/ lteb b a = true.
Proof.
  induction a as [|a IH]; intros [|b]; simpl;
    try (left; reflexivity); try (right; reflexivity).
  exact (IH b).
Qed.

Lemma dLte_trans : forall a b c, dLte a b = true -> dLte b c = true -> dLte a c = true.
Proof.
  intros [x| |] [y| |] [z| |] p q; simpl in *;
    try reflexivity; try discriminate.
  exact (lteb_trans z y x q p).
Qed.

Lemma dLte_antisym : forall a b, dLte a b = true -> dLte b a = true -> a = b.
Proof.
  intros [x| |] [y| |] p q; simpl in *;
    try reflexivity; try discriminate.
  rewrite (lteb_antisym x y q p); reflexivity.
Qed.

Lemma dLte_total : forall a b, dLte a b = true \/ dLte b a = true.
Proof.
  intros [x| |] [y| |]; simpl;
    try (left; reflexivity); try (right; reflexivity).
  exact (lteb_total y x).
Qed.

Theorem fateLte_trans : forall x y z,
  fateLte x y = true -> fateLte y z = true -> fateLte x z = true.
Proof.
  intros [|a| | |] [|b| | |] [|c| | |] p q; simpl in *;
    try reflexivity; try discriminate.
  exact (dLte_trans a b c p q).
Qed.

Theorem fateLte_antisym : forall x y,
  fateLte x y = true -> fateLte y x = true -> x = y.
Proof.
  intros [|a| | |] [|b| | |] p q; simpl in *;
    try reflexivity; try discriminate.
  rewrite (dLte_antisym a b p q); reflexivity.
Qed.

Theorem fateLte_total : forall x y, fateLte x y = true \/ fateLte y x = true.
Proof.
  intros [|a| | |] [|b| | |]; simpl;
    try (left; reflexivity); try (right; reflexivity).
  exact (dLte_total a b).
Qed.

(* A2-chain as one statement: the four laws of a total order. *)
Theorem fate_isTotalOrder :
  (forall x, fateLte x x = true) /\
  (forall x y z, fateLte x y = true -> fateLte y z = true -> fateLte x z = true) /\
  (forall x y, fateLte x y = true -> fateLte y x = true -> x = y) /\
  (forall x y, fateLte x y = true \/ fateLte y x = true).
Proof.
  exact (conj fateLte_refl (conj fateLte_trans (conj fateLte_antisym fateLte_total))).
Qed.

Theorem dLte_isTotalOrder :
  (forall a, dLte a a = true) /\
  (forall a b c, dLte a b = true -> dLte b c = true -> dLte a c = true) /\
  (forall a b, dLte a b = true -> dLte b a = true -> a = b) /\
  (forall a b, dLte a b = true \/ dLte b a = true).
Proof.
  exact (conj dLte_refl (conj dLte_trans (conj dLte_antisym dLte_total))).
Qed.

Lemma bondLte_trans : forall x y z,
  bondLte x y = true -> bondLte y z = true -> bondLte x z = true.
Proof. intros [] [] [] p q; simpl in *; try reflexivity; try discriminate. Qed.

Lemma mergeLte_trans : forall x y z,
  mergeLte x y = true -> mergeLte y z = true -> mergeLte x z = true.
Proof. intros [] [] [] p q; simpl in *; try reflexivity; try discriminate. Qed.

(* ------------------------------------------------------------------ *)
(* retention-order (TB.OrderLaws): ⊑ is a decidable preorder.           *)
(* ------------------------------------------------------------------ *)

Lemma andb_true6 : forall a b c d e f,
  andb a (andb b (andb c (andb d (andb e f)))) = true ->
  a = true /\ b = true /\ c = true /\ d = true /\ e = true /\ f = true.
Proof.
  intros [] [] [] [] [] [] p; simpl in p; try discriminate;
    repeat split; reflexivity.
Qed.

Lemma andb_intro6 : forall a b c d e f,
  a = true -> b = true -> c = true -> d = true -> e = true -> f = true ->
  andb a (andb b (andb c (andb d (andb e f)))) = true.
Proof.
  intros a b c d e f pa pb pc pd pe pf.
  rewrite pa, pb, pc, pd, pe, pf; reflexivity.
Qed.

Theorem gle_trans : forall g h k, gle g h -> gle h k -> gle g k.
Proof.
  intros [q1 b1 c1 r1 bo1 m1] [q2 b2 c2 r2 bo2 m2] [q3 b3 c3 r3 bo3 m3] p p';
    unfold gle, gradeLte in *; simpl in *.
  destruct (andb_true6 _ _ _ _ _ _ p) as [pq [pb [pc [pr [pbo pm]]]]].
  destruct (andb_true6 _ _ _ _ _ _ p') as [pq' [pb' [pc' [pr' [pbo' pm']]]]].
  apply andb_intro6.
  - exact (fateLte_trans _ _ _ pq pq').
  - exact (fateLte_trans _ _ _ pb pb').
  - exact (fateLte_trans _ _ _ pc pc').
  - exact (fateLte_trans _ _ _ pr pr').
  - exact (bondLte_trans _ _ _ pbo pbo').
  - exact (mergeLte_trans _ _ _ pm pm').
Qed.

Theorem gle_dec : forall g h, {gle g h} + {~ gle g h}.
Proof.
  intros g h; unfold gle; destruct (gradeLte g h).
  - left; reflexivity.
  - right; discriminate.
Defined.

(* ------------------------------------------------------------------ *)
(* L4-fidelity (TB.Order): dplus is monotone in each argument.          *)
(* ------------------------------------------------------------------ *)

Lemma lteb_suc_right : forall a b, lteb a b = true -> lteb a (S b) = true.
Proof.
  induction a as [|a IH]; intros [|b] p; simpl in *;
    try reflexivity; try discriminate.
  exact (IH b p).
Qed.

Lemma lteb_self_plus : forall m n, lteb m (m + n) = true.
Proof. induction m as [|m IH]; intros n; simpl; [reflexivity | apply IH]. Qed.

Lemma lteb_plus_left : forall m n, lteb n (m + n) = true.
Proof.
  induction m as [|m IH]; intros n; simpl.
  - apply lteb_refl.
  - apply lteb_suc_right, IH.
Qed.

Lemma lteb_plus_monoL : forall c a b, lteb a b = true -> lteb (c + a) (c + b) = true.
Proof. induction c as [|c IH]; intros a b p; simpl; [exact p | exact (IH a b p)]. Qed.

Lemma lteb_plus_monoR : forall a b c, lteb a b = true -> lteb (a + c) (b + c) = true.
Proof.
  induction a as [|a IH]; intros [|b] c p; simpl in *; try discriminate.
  - apply lteb_refl.
  - exact (lteb_plus_left (S b) c).
  - exact (IH b c p).
Qed.

Theorem dplusMonoR : forall c a b, dLte a b = true -> dLte (dplus c a) (dplus c b) = true.
Proof.
  intros [m| |] [x| |] [y| |] p; simpl in *; try reflexivity; try discriminate.
  exact (lteb_plus_monoL m y x p).
Qed.

Theorem dplusMonoL : forall a b c, dLte a b = true -> dLte (dplus a c) (dplus b c) = true.
Proof.
  intros [x| |] [y| |] [n| |] p; simpl in *; try reflexivity; try discriminate.
  exact (lteb_plus_monoR y x n p).
Qed.

Lemma dplusRetLteR : forall d a, dLte (dplus d a) d = true.
Proof.
  intros [m| |] [n| |]; simpl; try reflexivity.
  apply lteb_self_plus.
Qed.

Lemma dplusRetLteL : forall a e, dLte (dplus a e) e = true.
Proof.
  intros [m| |] [n| |]; simpl; try reflexivity.
  apply lteb_plus_left.
Qed.

(* ------------------------------------------------------------------ *)
(* L4-fate (TB.Order).                                                  *)
(* ------------------------------------------------------------------ *)

Theorem fateL4MonoR : forall h x y,
  fateLte x y = true -> fateLte (fcomp h x) (fcomp h y) = true.
Proof.
  intros [|d| | |] [|a| | |] [|b| | |] p; simpl in *;
    first [ reflexivity | discriminate | exact p | apply dLte_refl
          | apply dplusRetLteR | exact (dplusMonoR d a b p) ].
Qed.

Theorem fateL4MonoL : forall x y h,
  fateLte x y = true -> fateLte (fcomp x h) (fcomp y h) = true.
Proof.
  intros [|a| | |] [|b| | |] [|e| | |] p; simpl in *;
    first [ reflexivity | discriminate | exact p | apply dLte_refl
          | apply dplusRetLteL | exact (dplusMonoL a b e p) ].
Qed.

(* ------------------------------------------------------------------ *)
(* L4-bond-merge (TB.Monotone).                                         *)
(* ------------------------------------------------------------------ *)

Theorem bondL4MonoR : forall h x y,
  bondLte x y = true -> bondLte (bcomp h x) (bcomp h y) = true.
Proof. intros [] [] [] p; simpl in *; try reflexivity; try discriminate. Qed.

Theorem bondL4MonoL : forall x y h,
  bondLte x y = true -> bondLte (bcomp x h) (bcomp y h) = true.
Proof. intros [] [] [] p; simpl in *; try reflexivity; try discriminate. Qed.

Theorem mergeL4MonoR : forall h x y,
  mergeLte x y = true -> mergeLte (mcomp h x) (mcomp h y) = true.
Proof. intros [] [] [] p; simpl in *; try reflexivity; try discriminate. Qed.

Theorem mergeL4MonoL : forall x y h,
  mergeLte x y = true -> mergeLte (mcomp x h) (mcomp y h) = true.
Proof. intros [] [] [] p; simpl in *; try reflexivity; try discriminate. Qed.

(* ------------------------------------------------------------------ *)
(* L4-lifting (TB.Monotone): gcomp is ⊑-monotone.                       *)
(* ------------------------------------------------------------------ *)

Theorem gradeL4MonoR : forall k g h, gle g h -> gle (gcomp k g) (gcomp k h).
Proof.
  intros [q b c r bo m] [q1 b1 c1 r1 bo1 m1] [q2 b2 c2 r2 bo2 m2] p;
    unfold gle, gradeLte, gcomp in *; simpl in *.
  destruct (andb_true6 _ _ _ _ _ _ p) as [pq [pb [pc [pr [pbo pm]]]]].
  apply andb_intro6.
  - exact (fateL4MonoR q _ _ pq).
  - exact (fateL4MonoR b _ _ pb).
  - exact (fateL4MonoR c _ _ pc).
  - exact (fateL4MonoR r _ _ pr).
  - exact (bondL4MonoR bo _ _ pbo).
  - exact (mergeL4MonoR m _ _ pm).
Qed.

Theorem gradeL4MonoL : forall g h k, gle g h -> gle (gcomp g k) (gcomp h k).
Proof.
  intros [q1 b1 c1 r1 bo1 m1] [q2 b2 c2 r2 bo2 m2] [q b c r bo m] p;
    unfold gle, gradeLte, gcomp in *; simpl in *.
  destruct (andb_true6 _ _ _ _ _ _ p) as [pq [pb [pc [pr [pbo pm]]]]].
  apply andb_intro6.
  - exact (fateL4MonoL _ _ q pq).
  - exact (fateL4MonoL _ _ b pb).
  - exact (fateL4MonoL _ _ c pc).
  - exact (fateL4MonoL _ _ r pr).
  - exact (bondL4MonoL _ _ bo pbo).
  - exact (mergeL4MonoL _ _ m pm).
Qed.

Theorem gcomp_mono : forall g1 g2 h1 h2,
  gle g1 g2 -> gle h1 h2 -> gle (gcomp g1 h1) (gcomp g2 h2).
Proof.
  intros g1 g2 h1 h2 p q.
  exact (gle_trans _ _ _ (gradeL4MonoL g1 g2 h1 p) (gradeL4MonoR g2 h1 h2 q)).
Qed.

(* ------------------------------------------------------------------ *)
(* Definition bridge (TB.Bridge). The same six literals as the Agda    *)
(* and the Lean: if this file's restatement of any of the six          *)
(* definitions disagrees with the Agda at a sample point, the matching  *)
(* bridge theorem fails. Bond and Merge are covered exhaustively; Fate  *)
(* on nine points, top to bottom. Codes as in TB/Bridge.agda.           *)
(* ------------------------------------------------------------------ *)

Local Open Scope list_scope.

Definition b2n (b : bool) : nat := match b with true => 1 | false => 0 end.

Definition fcode (f : Fate) : nat :=
  match f with
  | present         => 0
  | atten (Q n)     => 10 + n
  | atten total     => 1
  | atten unknown   => 2
  | predicated      => 3
  | dropped         => 4
  | falsified       => 5
  end.

Definition bcode (b : Bond) : nat :=
  match b with intact => 0 | withheld => 1 | severed => 2 | misbound => 3 end.

Definition mcode (m : Merge) : nat :=
  match m with single => 0 | fused => 1 | conflated => 2 end.

Definition sampleF : list Fate :=
  present :: atten (Q 0) :: atten (Q 2) :: atten (Q 5) :: atten total
  :: atten unknown :: predicated :: dropped :: falsified :: nil.

Definition sampleB : list Bond := intact :: withheld :: severed :: misbound :: nil.

Definition sampleM : list Merge := single :: fused :: conflated :: nil.

Fixpoint lmap {A B : Type} (f : A -> B) (xs : list A) : list B :=
  match xs with nil => nil | x :: t => f x :: lmap f t end.

Fixpoint lappend {A : Type} (xs ys : list A) : list A :=
  match xs with nil => ys | x :: t => x :: lappend t ys end.

Fixpoint lconcatMap {A B : Type} (f : A -> list B) (xs : list A) : list B :=
  match xs with nil => nil | x :: t => lappend (f x) (lconcatMap f t) end.

Definition tbl {A : Type} (f : A -> A -> nat) (xs : list A) : list nat :=
  lconcatMap (fun x => lmap (f x) xs) xs.

Definition fateLteTable_literal : list nat :=
    1 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 1 :: 1 :: 0 :: 0 ::
    0 :: 0 :: 0 :: 0 :: 0 :: 1 :: 1 :: 1 :: 0 :: 0 :: 0 :: 0 :: 0 ::
    0 :: 1 :: 1 :: 1 :: 1 :: 0 :: 0 :: 0 :: 0 :: 0 :: 1 :: 1 :: 1 ::
    1 :: 1 :: 0 :: 0 :: 0 :: 0 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 0 ::
    0 :: 0 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 0 :: 0 :: 1 :: 1 ::
    1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 0 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 ::
    1 :: 1 :: 1 :: nil.

Definition fcompTable_literal : list nat :=
    0 :: 10 :: 12 :: 15 :: 1 :: 2 :: 3 :: 4 :: 5 :: 10 :: 10 :: 12 ::
    15 :: 1 :: 2 :: 3 :: 4 :: 5 :: 12 :: 12 :: 14 :: 17 :: 1 :: 2 ::
    3 :: 4 :: 5 :: 15 :: 15 :: 17 :: 20 :: 1 :: 2 :: 3 :: 4 :: 5 ::
    1 :: 1 :: 1 :: 1 :: 1 :: 2 :: 3 :: 4 :: 5 :: 2 :: 2 :: 2 :: 2 ::
    2 :: 2 :: 3 :: 4 :: 5 :: 3 :: 3 :: 3 :: 3 :: 3 :: 3 :: 3 :: 4 ::
    5 :: 4 :: 4 :: 4 :: 4 :: 4 :: 4 :: 4 :: 4 :: 5 :: 5 :: 5 :: 5 ::
    5 :: 5 :: 5 :: 5 :: 5 :: 5 :: nil.

Definition bondLteTable_literal : list nat :=
    1 :: 0 :: 0 :: 0 :: 1 :: 1 :: 0 :: 0 :: 1 :: 1 :: 1 :: 0 :: 1 ::
    1 :: 1 :: 1 :: nil.

Definition bcompTable_literal : list nat :=
    0 :: 1 :: 2 :: 3 :: 1 :: 1 :: 2 :: 3 :: 2 :: 2 :: 2 :: 3 :: 3 ::
    3 :: 3 :: 3 :: nil.

Definition mergeLteTable_literal : list nat :=
    1 :: 0 :: 0 :: 1 :: 1 :: 0 :: 1 :: 1 :: 1 :: nil.

Definition mcompTable_literal : list nat :=
    0 :: 1 :: 2 :: 1 :: 1 :: 2 :: 2 :: 2 :: 2 :: nil.

Theorem bridge_fateLte : tbl (fun x y => b2n (fateLte x y)) sampleF = fateLteTable_literal.
Proof. reflexivity. Qed.

Theorem bridge_fcomp : tbl (fun x y => fcode (fcomp x y)) sampleF = fcompTable_literal.
Proof. reflexivity. Qed.

Theorem bridge_bondLte : tbl (fun x y => b2n (bondLte x y)) sampleB = bondLteTable_literal.
Proof. reflexivity. Qed.

Theorem bridge_bcomp : tbl (fun x y => bcode (bcomp x y)) sampleB = bcompTable_literal.
Proof. reflexivity. Qed.

Theorem bridge_mergeLte : tbl (fun x y => b2n (mergeLte x y)) sampleM = mergeLteTable_literal.
Proof. reflexivity. Qed.

Theorem bridge_mcomp : tbl (fun x y => mcode (mcomp x y)) sampleM = mcompTable_literal.
Proof. reflexivity. Qed.
