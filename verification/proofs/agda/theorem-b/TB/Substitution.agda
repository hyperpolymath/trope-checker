{-# OPTIONS --safe --without-K #-}
-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
--
-- Theorem B, Target 2 — substitution-admissibility / reindexing: "tropes follow
-- values through cut". The CORE lemma.
--
-- RESULT (honest, two halves divided exactly by F2):
--
--  PROVED  (value substitution, grade-EXACT). Substitution by ε-graded terms
--          (values) preserves the host grade g EXACTLY. The substitution lemma
--          `subst : Subst Γ Δ → Γ ⊢ A ! g → Δ ⊢ A ! g` IS this statement: the
--          output grade is the SAME g, with no ▷-reorder anywhere. It is
--          insensitive to F2 precisely because a value carries ε, and ε is a
--          two-sided unit of ▷ (gmonoid-unitL/R), so non-commutativity is inert.
--          This is the machine-checked form of "tropes follow values through cut".
--
--  REFUTED (symmetric computational cut). The `let`/bind seam composes grades in
--          ONE fixed orientation g₁ ▷ g₂ (bound-effect first). The mirror
--          orientation g₂ ▷ g₁ is FALSE on the nose; the disproof is the F2
--          witness (dropped/falsified) transported to the cut. So the value
--          lemma is SHARP: it cannot be generalised to an orientation-free
--          computational substitution. This is the precise F2 boundary — not a
--          gap in the proof, but a theorem about what the structure forbids.

module TB.Substitution where

open import Data.Product.Base using (Σ; ∃; _×_) renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Relation.Nullary using (¬_)

open import TB.Grade
open import TB.Order using (_⊑_)
open import TB.Syntax

--------------------------------------------------------------------------------
-- Renaming (grade-preserving — renaming never touches the grade index).
--------------------------------------------------------------------------------

Rename : Ctx → Ctx → Set
Rename Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

ext : ∀ {Γ Δ B} → Rename Γ Δ → Rename (Γ , B) (Δ , B)
ext ρ here      = here
ext ρ (there x) = there (ρ x)

rename : ∀ {Γ Δ A g} → Rename Γ Δ → Γ ⊢ A ! g → Δ ⊢ A ! g
rename ρ (`var x)         = `var (ρ x)
rename ρ (`lam d)         = `lam (rename (ext ρ) d)
rename ρ (`app f x)       = `app (rename ρ f) (rename ρ x)
rename ρ (`letc d e)      = `letc (rename ρ d) (rename (ext ρ) e)
rename ρ (`preserve d)    = `preserve (rename ρ d)
rename ρ (`attenuate δ d) = `attenuate δ (rename ρ d)
rename ρ (`project d)     = `project (rename ρ d)
rename ρ (`detach d)      = `detach (rename ρ d)
rename ρ (`collapse d)    = `collapse (rename ρ d)
rename ρ (`sub p d)       = `sub p (rename ρ d)

--------------------------------------------------------------------------------
-- THE substitution lemma (Target 2, value/ε form). A substitution maps each
-- variable to an ε-graded (value) term; `subst` then preserves the host grade
-- g EXACTLY. The very type of `subst` is the theorem.
--------------------------------------------------------------------------------

-- A simultaneous substitution: each variable goes to a VALUE (grade ε).
Subst : Ctx → Ctx → Set
Subst Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A ! ε

exts : ∀ {Γ Δ B} → Subst Γ Δ → Subst (Γ , B) (Δ , B)
exts σ here      = `var here
exts σ (there x) = rename there (σ x)

-- subst : preserves the grade g EXACTLY (no ▷ appears in the conclusion's grade).
subst : ∀ {Γ Δ A g} → Subst Γ Δ → Γ ⊢ A ! g → Δ ⊢ A ! g
subst σ (`var x)         = σ x
subst σ (`lam d)         = `lam (subst (exts σ) d)
subst σ (`app f x)       = `app (subst σ f) (subst σ x)
subst σ (`letc d e)      = `letc (subst σ d) (subst (exts σ) e)
subst σ (`preserve d)    = `preserve (subst σ d)
subst σ (`attenuate δ d) = `attenuate δ (subst σ d)
subst σ (`project d)     = `project (subst σ d)
subst σ (`detach d)      = `detach (subst σ d)
subst σ (`collapse d)    = `collapse (subst σ d)
subst σ (`sub p d)       = `sub p (subst σ d)

-- Single substitution of one value for the most-recent variable, grade-exact.
σ₀ : ∀ {Γ B} → Γ ⊢ B ! ε → Subst (Γ , B) Γ
σ₀ v here      = v
σ₀ v (there x) = `var x

infix 8 _[_]
_[_] : ∀ {Γ B A g} → (Γ , B) ⊢ A ! g → Γ ⊢ B ! ε → Γ ⊢ A ! g
d [ v ] = subst (σ₀ v) d

-- The named headline: cut by a value preserves the grade EXACTLY (the content
-- of "tropes follow values through cut"). Returns the contractum at grade g.
cut-preserves-grade : ∀ {Γ B A g} → (Γ , B) ⊢ A ! g → Γ ⊢ B ! ε → Γ ⊢ A ! g
cut-preserves-grade d v = d [ v ]

--------------------------------------------------------------------------------
-- The cut's ORIENTATION (the F2 boundary). The `let` seam composes g₁ ▷ g₂
-- (bound-effect first). The symmetric orientation is refuted.
--------------------------------------------------------------------------------

-- The left-oriented cut grade is definitional: `letc` at g₁ ▷ g₂.
cut-left-grade : ∀ {Γ A B g₁ g₂} → Γ ⊢ A ! g₁ → (Γ , A) ⊢ B ! g₂ → Γ ⊢ B ! (g₁ ▷ g₂)
cut-left-grade d e = `letc d e

-- REFUTATION: the cut grade is NOT reorderable — there are computations whose
-- forward composition g₁ ▷ g₂ differs from the swapped g₂ ▷ g₁ (F2). Witnessed
-- at the two disagreeing absorbing fate heads (dropped / falsified).
cut-orientation-matters : Σ Grade (λ g₁ → Σ Grade (λ g₂ → (g₁ ▷ g₂) ≢ (g₂ ▷ g₁)))
cut-orientation-matters = gA ,, gB ,, λ eq → dropped≢falsified (cong fQuality eq)

-- The general "symmetric computational cut" law is uninhabited: one cannot have
-- a substitution principle that composes grades in EITHER order. (= grade-not-comm,
-- restated as the Target-2 sharpness theorem.)
cut-symmetric-fails : ¬ (∀ (g₁ g₂ : Grade) → g₁ ▷ g₂ ≡ g₂ ▷ g₁)
cut-symmetric-fails = grade-not-comm
