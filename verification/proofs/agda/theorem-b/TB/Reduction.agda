{-# OPTIONS --safe --without-K #-}
-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
--
-- Theorem B, Target 3 — subject reduction, RESPECTING the three-tier F4 boundary.
--
-- INTRINSIC SUBJECT REDUCTION. The reduction relation _↝_ is indexed at a FIXED
-- (Γ , A , g): a step relates a redex and a contractum at the SAME type AND the
-- SAME grade. So "subject reduction" — type and grade are preserved by a step —
-- holds BY CONSTRUCTION: it is the well-typedness of _↝_'s constructors. The
-- non-trivial content is that the β / let-value steps CAN be typed at one grade
-- index, which rests on (i) Target 2's grade-exact value substitution and (ii)
-- the unit laws collapsing (ε ▷ ε) ▷ g and ε ▷ g to g definitionally.
--
-- RESPECTING THE BOUNDARY (F4):
--  * For our reductions the grade is preserved EXACTLY, so the tier is preserved
--    EXACTLY (the strongest form of "respecting the boundary": no tier moves).
--  * For the grade-COMPOSING operations (the effect formers g ▷ atom, and any
--    effect-sequencing a richer operational semantics would add) the boundary is
--    respected in the CLOSURE sense established in TB.Tier: deceptive stays
--    deceptive (L5 irreversibility, dynamic — two-sided since R-2026-07-07 (A1)),
--    the cancellative core stays in the core. The naive single-tier
--    meet-homomorphism STILL FAILS on the ratified carrier
--    (TB.Tier.fate-tier-meet-hom-fails, new witness: collapse discards the
--    deceptive fidelity-unknown inside atten) — which is why preservation is
--    closure, not homomorphism. (The historical L4 tripwire fate-L4-fails is
--    RETIRED: L4 holds on the ratified carrier, TB.Order.fateL4Mono{R,L};
--    exact grade preservation remains the stronger property used here.)
--
--  * fix / lfp (calculus §7) is NOT-REACHED. See the precise statement at the
--    foot of this module. No postulate is introduced for it.

module TB.Reduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import TB.Grade
open import TB.Syntax
open import TB.Substitution using (_[_])
open import TB.Tier
  using (tierOf; Deceptive; deceptive-absorbs-▷; IsCore; core-closed-▷)

--------------------------------------------------------------------------------
-- The reduction relation, intrinsically at a fixed grade index.
-- (Each constructor's well-typedness IS a subject-reduction case.)
--------------------------------------------------------------------------------

infix 2 _↝_
data _↝_ : ∀ {Γ A g} → Γ ⊢ A ! g → Γ ⊢ A ! g → Set where

  -- β: (λ e) applied to a value v reduces to e[v]. Redex grade (ε ▷ ε) ▷ g
  -- ≡ g definitionally; contractum grade g (Target 2). Same index ⇒ SR.
  β-app : ∀ {Γ A B g} (e : (Γ , A) ⊢ B ! g) (v : Γ ⊢ A ! ε)
        → `app (`lam e) v ↝ (e [ v ])

  -- let of a value: let x = v in e reduces to e[v]. Redex grade ε ▷ g ≡ g.
  β-let : ∀ {Γ A B g} (v : Γ ⊢ A ! ε) (e : (Γ , A) ⊢ B ! g)
        → `letc v e ↝ (e [ v ])

--------------------------------------------------------------------------------
-- Subject reduction + tier preservation (exact, for the value reductions).
--------------------------------------------------------------------------------

-- THE CONTENT of intrinsic subject reduction is the grade-COLLAPSE equations that
-- make _↝_ definable at a single index: a β-redex's grade (ε ▷ ε) ▷ g and a
-- let-value redex's grade ε ▷ g each equal the contractum's grade g, BY THE F1
-- UNIT LAWS. These are genuine monoid equations — the left-hand side is
-- syntactically distinct from the right — NOT the tautology g ≡ g. They are
-- exactly why the constructors of _↝_ typecheck at a fixed grade, i.e. why
-- subject reduction holds; the proof is `refl` only because the unit laws are
-- definitional in this carrier.
β-redex-grade : ∀ g → (ε ▷ ε) ▷ g ≡ g
β-redex-grade g = refl

let-redex-grade : ∀ g → ε ▷ g ≡ g
let-redex-grade g = refl

-- Hence each step RESPECTS the F4 tier boundary: the tier of the redex grade
-- equals the tier of the contractum grade — no tier moves across a β/let step.
-- (Non-vacuous: the arguments of tierOf differ syntactically.)
β-tier-preserved : ∀ g → tierOf ((ε ▷ ε) ▷ g) ≡ tierOf g
β-tier-preserved g = cong tierOf (β-redex-grade g)

let-tier-preserved : ∀ g → tierOf (ε ▷ g) ≡ tierOf g
let-tier-preserved g = cong tierOf (let-redex-grade g)

-- The intrinsic subject-reduction statement is the TYPE of _↝_ itself: a step
-- relates a redex and a contractum at the SAME (Γ , A , g). This projection just
-- extracts the well-typed-and-well-graded reduct; its FORCE is in _↝_'s indexing
-- (the grade-collapse equations above), not in this one line.
reduct : ∀ {Γ A g} {d d′ : Γ ⊢ A ! g} → d ↝ d′ → Γ ⊢ A ! g
reduct {d′ = d′} _ = d′

--------------------------------------------------------------------------------
-- The boundary under grade COMPOSITION (the effect formers). These link the
-- syntax (Target 1) to the F4 closures (TB.Tier): applying any further effect
-- to a deceptive computation keeps it deceptive — L5 irreversibility, made
-- dynamic in the calculus. (The same holds for project/detach/collapse/preserve;
-- attenuate shown as the representative.)
--------------------------------------------------------------------------------

attenuate-stays-deceptive : ∀ {Γ g} (δ : Δ) → Γ ⊢ ⋆Trope ! g
                          → Deceptive g → Deceptive (g ▷ atten-atom δ)
attenuate-stays-deceptive δ _ dec = deceptive-absorbs-▷ _ _ dec

project-stays-deceptive : ∀ {Γ g} → Γ ⊢ ⋆Trope ! g
                        → Deceptive g → Deceptive (g ▷ drop-atom)
project-stays-deceptive _ dec = deceptive-absorbs-▷ _ _ dec

-- And composing two cancellative-core computations stays in the core.
seq-stays-core : ∀ {Γ A B g₁ g₂} → Γ ⊢ A ! g₁ → (Γ , A) ⊢ B ! g₂
               → IsCore g₁ → IsCore g₂ → IsCore (g₁ ▷ g₂)
seq-stays-core {g₁ = g₁} {g₂ = g₂} _ _ c₁ c₂ = core-closed-▷ g₁ g₂ c₁ c₂

--------------------------------------------------------------------------------
-- fix / lfp — NOT-REACHED (precise statement; NO postulate).
--------------------------------------------------------------------------------
-- The calculus's general recursion (`fix`, §7) grades a recursive trope-
-- transformer by the LEAST FIXED POINT of its grade functional. Subject
-- reduction for the fix-unfold step
--
--     fix x. e  ↝  e [ fix x. e / x ]
--
-- is NOT-REACHED here, and is NOT postulated. Two things are genuinely missing,
-- exactly as flagged by the spec (§7, O4) and PROOF-STATUS:
--
--   (1) an OPERATIONAL model: there is no ↝ rule for fix and no definition of
--       the observed retention ρ against which grade soundness for the unfold
--       would be stated. (The spec is a type DISCIPLINE; reduction beyond β/let
--       is not given.)
--   (2) a LIMIT CARRIER for the lfp grade: ordering iterated unbounded
--       attenuation beyond ω is the open O4 fork (Conat-vs-tag). The lfp's
--       fidelity lands in the absorbing tops {total, unknown}, which ARE
--       ▷-fixed (TB.Grade.total-absorb-Q, unknown-absorbL) — so the GRADE is
--       tier-stable — but the operational unfold-preserves-tier step needs (1)+(2).
--
-- The honest verdict for fix-subject-reduction is therefore NOT-REACHED, with
-- the obstruction characterised: it is the missing operational semantics + the
-- O4 limit carrier, NOT a defect of the grade algebra (whose lfp endpoint is
-- already tier-stable).
