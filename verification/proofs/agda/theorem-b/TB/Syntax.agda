{-# OPTIONS --safe --without-K #-}
-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
--
-- Theorem B, Target 1 (encoding) — the trope-particularity calculus, INTRINSICALLY
-- typed, as a graded deductive system over the NON-COMMUTATIVE grade monoid ▷.
--
-- The judgement is Γ ⊢ A ! g ("produces an A with trope-effect grade g",
-- calculus §6). Terms are intrinsically indexed by BOTH the type A and the grade
-- g, so a derivation IS a well-typed-and-well-graded term: no separate typing
-- relation, no separate grade-soundness side condition.
--
-- DESIGN (per the FROZEN INTERFACE + design-panel findings):
--   * variables carry ε (the unit) by construction;
--   * each UNARY effect former POST-composes its atom on the RIGHT (g ▷ atom),
--     exactly the spec's `g ▷ drop(...)`, `g ▷ sever`, `g ▷ ε` shapes;
--   * the binary seams `app`/`let` put the EARLIER effect on the LEFT of ▷
--     (CBV: argument-first), `gx ▷ gf ▷ g` and `g₁ ▷ g₂` — F2 makes this ORDER
--     load-bearing and not reorderable (see TB.Substitution.cut-not-reorderable);
--   * T-Sub is a LEAF constructor, one-sided (downward in retention, g′ ⊑ g);
--     it is deliberately NOT pushed through the formers (that would assume the
--     monotonicity that fate refutes, TB.Tier.fate-L4-fails).
--
-- SCOPE (honest): the field-presence indexing of Trope[S] (the S ⊆ Φ subtyping
-- and FloatingQuality presence-tracking) is modelled at coarse granularity — a
-- single fully-present trope type ⋆Trope, with detach/collapse producing the
-- type CHANGES (⋆Floating / ⋆Base) but not the per-field presence bookkeeping.
-- The GRADE discipline (the object of Theorem B) is exact; the presence type
-- refinement, already carried in the Idris ground truth, is elided here. `fuse`
-- (the sole binary former, needing the retention-join ⊔) is likewise omitted
-- from the intrinsic core; its grade rule is recorded in the interface report.

module TB.Syntax where

open import TB.Grade
open import TB.Order using (_⊑_)

--------------------------------------------------------------------------------
-- Types: a trope, a floating quality, a collapse codomain, and the latent-grade
-- arrow A ─g→ B (calculus §6: "function types carry latent grade").
--------------------------------------------------------------------------------

infixr 7 _⇒[_]_
data Ty : Set where
  ⋆Trope    : Ty
  ⋆Floating : Ty
  ⋆Base     : Ty
  _⇒[_]_    : Ty → Grade → Ty → Ty

infixl 5 _,_
data Ctx : Set where
  ∅   : Ctx
  _,_ : Ctx → Ty → Ctx

infix 4 _∋_
data _∋_ : Ctx → Ty → Set where
  here  : ∀ {Γ A}   → (Γ , A) ∋ A
  there : ∀ {Γ A B} → Γ ∋ A → (Γ , B) ∋ A

--------------------------------------------------------------------------------
-- The effect ATOMS (calculus §6), as concrete grade constants. Each unary
-- former post-composes one of these. Reproduced from the spec's atom definitions.
--------------------------------------------------------------------------------

-- preserve introduces ε (T-Preserve: g ▷ ε).
-- atten(δ): fate = Attenuated(δ) on every (present) field; bond/merge unchanged.
atten-atom : Δ → Grade
atten-atom δ = mkGrade (atten δ) (atten δ) (atten δ) (atten δ) intact single

-- drop(bearer) representative (T-Project): fate(bearer)=Dropped, bond=Withheld.
drop-atom : Grade
drop-atom = mkGrade present dropped present present withheld single

-- sever (T-Detach): fate(quality)=Present, other fates Dropped, bond=Severed.
sever-atom : Grade
sever-atom = mkGrade present dropped dropped dropped severed single

-- predicate(P) (T-Collapse): fate(quality)=Predicated, others Dropped, bond=Withheld.
predicate-atom : Grade
predicate-atom = mkGrade predicated dropped dropped dropped withheld single

--------------------------------------------------------------------------------
-- The intrinsic typing/grading relation.
--------------------------------------------------------------------------------

infix 3 _⊢_!_
data _⊢_!_ : Ctx → Ty → Grade → Set where

  -- variables carry ε
  `var : ∀ {Γ A}
       → Γ ∋ A
       → Γ ⊢ A ! ε

  -- abstraction is pure (ε); the body's grade g becomes the arrow's latent grade
  `lam : ∀ {Γ A B g}
       → (Γ , A) ⊢ B ! g
       → Γ ⊢ (A ⇒[ g ] B) ! ε

  -- application, CBV: argument effect gx FIRST (leftmost), then function gf, then latent g
  `app : ∀ {Γ A B g gf gx}
       → Γ ⊢ (A ⇒[ g ] B) ! gf
       → Γ ⊢ A ! gx
       → Γ ⊢ B ! (gx ▷ gf ▷ g)

  -- the composition seam (let / monadic bind): bound effect g₁ FIRST (left), body g₂ second
  `letc : ∀ {Γ A B g₁ g₂}
        → Γ ⊢ A ! g₁
        → (Γ , A) ⊢ B ! g₂
        → Γ ⊢ B ! (g₁ ▷ g₂)

  -- T-Preserve
  `preserve : ∀ {Γ g}
            → Γ ⊢ ⋆Trope ! g
            → Γ ⊢ ⋆Trope ! (g ▷ ε)

  -- T-Attenuate
  `attenuate : ∀ {Γ A g} (δ : Δ)
             → Γ ⊢ A ! g
             → Γ ⊢ A ! (g ▷ atten-atom δ)

  -- T-Project (the bearer-drop representative)
  `project : ∀ {Γ g}
           → Γ ⊢ ⋆Trope ! g
           → Γ ⊢ ⋆Trope ! (g ▷ drop-atom)

  -- T-Detach (type changes to ⋆Floating)
  `detach : ∀ {Γ g}
          → Γ ⊢ ⋆Trope ! g
          → Γ ⊢ ⋆Floating ! (g ▷ sever-atom)

  -- T-Collapse (type changes to the codomain ⋆Base)
  `collapse : ∀ {Γ g}
            → Γ ⊢ ⋆Trope ! g
            → Γ ⊢ ⋆Base ! (g ▷ predicate-atom)

  -- T-Sub: subsumption, one-sided (weaken DOWNWARD in retention only)
  `sub : ∀ {Γ A g g′}
       → g′ ⊑ g
       → Γ ⊢ A ! g
       → Γ ⊢ A ! g′
