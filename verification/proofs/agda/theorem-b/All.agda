{-# OPTIONS --safe --without-K #-}
-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
--
-- Theorem B — whole-development typecheck. `agda All.agda` exiting 0 under
-- --safe --without-K certifies the entire metatheory development.
module All where

open import TB.Grade
open import TB.Order
open import TB.Tier
open import TB.Syntax
open import TB.Substitution
open import TB.Reduction
open import TB.Honest
