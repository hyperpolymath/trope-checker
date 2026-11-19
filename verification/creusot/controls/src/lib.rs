// SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0
//
// Planted false contracts. Every item here is FALSE. run.sh enables one feature
// at a time and requires Creusot to fail on it. See ../README.adoc.
#![allow(dead_code, unused_imports)]
#![cfg(creusot)]

use creusot_std::prelude::*;
use tropecheck_rs::creusot_spec::*;
use tropecheck_rs::*;

/// c00: the solver sanity control. `false` must never be provable.
#[cfg(feature = "c00_false")]
#[ensures(false)]
pub fn c00() {}

/// c01: the pre-A1 law "the drop swallows the lie". Ratified A1 says the lie
/// survives: compose(Dropped, Falsified) = Falsified.
#[cfg(feature = "c01_pre_a1_drop_absorbs_lie")]
#[ensures(result.deep_model() == FateM::Dropped)]
pub fn c01() -> Fate {
    fate_compose(&Fate::Dropped, &Fate::Falsified)
}

/// c02: calling dadd with no overflow precondition (owner ruling 1: overflow is
/// a precondition proved at callers). Creusot must fail dadd's precondition.
#[cfg(feature = "c02_dadd_without_overflow_precondition")]
pub fn c02(a: &Delta, b: &Delta) -> Delta {
    dadd(a, b)
}

/// c03: meet is a lower bound with no honesty precondition. False in Rust:
/// meet(Falsified, Present) = Dropped, and Dropped is not below Falsified. This
/// is the live control for the deceptive-order divergence.
#[cfg(feature = "c03_meet_lower_bound_off_honest")]
#[ensures(fate_le_m(result.deep_model(), a.deep_model()))]
pub fn c03(a: &Fate, b: &Fate) -> Fate {
    fate_meet(a, b)
}

/// c04: the converse of A2. A checkbox is not retained by nothing.
#[cfg(feature = "c04_predicated_le_dropped")]
#[ensures(result)]
pub fn c04() -> bool {
    fate_le(&Fate::Predicated, &Fate::Dropped)
}

/// c05: the Rust fate order equals the Agda fateLte on ALL inputs. False on
/// deceptive inputs (Agda: Falsified ⊑ everything; Rust: only itself).
#[cfg(feature = "c05_agda_correspondence_everywhere")]
#[logic]
#[ensures(fate_le_m(a, b) == agda_fate_le(a, b))]
pub fn c05(a: FateM, b: FateM) {}

/// c06: L4 without non-negative losses. Atten(Q -1) ⊑ Present, but composing
/// both with Atten(Q 1) gives Atten(Q 0) ⋢ Atten(Q 1).
#[cfg(feature = "c06_l4_without_nonneg")]
#[logic]
#[requires(fate_le_m(a, b))]
#[ensures(fate_le_m(fate_compose_m(a, c), fate_compose_m(b, c)))]
pub fn c06(a: FateM, b: FateM, c: FateM) {}

/// c07: grade meet is a lower bound with no honesty precondition.
#[cfg(feature = "c07_meet_lower_bound_grade_off_honest")]
#[logic]
#[ensures(grade_le_m(grade_meet_m(a, b), a))]
pub fn c07(a: GradeM, b: GradeM) {}

/// c08: violations never reports anything, whatever the floor.
#[cfg(feature = "c08_violations_empty_always")]
#[ensures(result@.len() == 0)]
pub fn c08(fl: &Floor, g: &Grade) -> Vec<String> {
    violations(fl, g)
}
