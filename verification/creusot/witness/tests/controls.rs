// SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0
//
// One test per planted control in ../controls. Each test PASSES on the shipped
// code exactly when that control's claim is FALSE, by running a concrete
// counterexample. run.sh requires every test here to pass; a witness that does
// not hold makes the Creusot gate red.
use tropecheck_rs::{
    dadd, epsilon, fate_compose, fate_le, fate_meet, grade_le, grade_meet, violations, Delta, Fate,
    Floor,
};

fn floor_q(q: Fate) -> Floor {
    Floor {
        q: Some(q),
        b: None,
        c: None,
        r: None,
        bond: None,
        merge: None,
    }
}

/// c00 claims `ensures(false)`: false for every input, nothing to run.
#[test]
fn c00_false() {
    let claim = false;
    assert!(!claim);
}

/// c01 claims compose(Dropped, Falsified) = Dropped. A1: it is Falsified.
#[test]
fn c01_pre_a1_drop_absorbs_lie() {
    let r = fate_compose(&Fate::Dropped, &Fate::Falsified);
    assert!(r == Fate::Falsified);
    assert!(r != Fate::Dropped);
}

/// c02 calls dadd with no overflow precondition. Q(i64::MAX) + Q(1) overflows.
#[test]
#[should_panic(expected = "overflow")]
fn c02_dadd_without_overflow_precondition() {
    let _ = dadd(&Delta::Q(i64::MAX), &Delta::Q(1));
}

/// c03 claims meet(a, b) ⊑ a for all fates. a = Falsified, b = Present:
/// meet = Dropped, and Dropped ⋢ Falsified in the Rust order.
#[test]
fn c03_meet_lower_bound_off_honest() {
    let m = fate_meet(&Fate::Falsified, &Fate::Present);
    assert!(m == Fate::Dropped);
    assert!(!fate_le(&m, &Fate::Falsified));
}

/// c04 claims Predicated ⊑ Dropped. A2 says the converse only.
#[test]
fn c04_predicated_le_dropped() {
    assert!(!fate_le(&Fate::Predicated, &Fate::Dropped));
}

/// c05 claims the Rust fate order equals Agda's fateLte everywhere. Agda has
/// `fateLte falsified _ = true` (TB/Order.agda, checked below); Rust says
/// Falsified ⋢ Present.
#[test]
fn c05_agda_correspondence_everywhere() {
    let agda = include_str!("../../../proofs/agda/theorem-b/TB/Order.agda");
    assert!(agda.contains("fateLte falsified  _          = true"));
    assert!(!fate_le(&Fate::Falsified, &Fate::Present));
}

/// c06 claims L4 without non-negative losses. a = Atten(-1) ⊑ b = Present, but
/// composing both with c = Atten(1) gives Atten(0) ⋢ Atten(1).
#[test]
fn c06_l4_without_nonneg() {
    let (a, b, c) = (
        Fate::Atten(Delta::Q(-1)),
        Fate::Present,
        Fate::Atten(Delta::Q(1)),
    );
    assert!(fate_le(&a, &b));
    assert!(!fate_le(&fate_compose(&a, &c), &fate_compose(&b, &c)));
}

/// c07 claims grade_meet(a, b) ⊑ a for all grades. a.q = Falsified, b = ε.
#[test]
fn c07_meet_lower_bound_grade_off_honest() {
    let mut a = epsilon();
    a.q = Fate::Falsified;
    let m = grade_meet(&a, &epsilon());
    assert!(!grade_le(&m, &a));
}

/// c08 claims violations is always empty. Floor q = Present against q = Dropped.
#[test]
fn c08_violations_empty_always() {
    let mut g = epsilon();
    g.q = Fate::Dropped;
    assert!(!violations(&floor_q(Fate::Present), &g).is_empty());
}
