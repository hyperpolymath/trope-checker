// SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0
//
// One test per mutant in ../mutants/MUTANTS, named by its id. Each test states
// the function's contract on one concrete input. run.sh requires every test to
// PASS on the shipped code, and the mutant's own test to FAIL on the mutated
// code: a concrete input on which the mutant breaks its contract.
use tropecheck_rs::{
    bond_compose, dadd, epsilon, fate_compose, fate_le, merge_compose, violations, Bond, Delta,
    Fate, Floor, Merge,
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

#[test]
fn m01_drop_swallows_lie() {
    assert!(fate_compose(&Fate::Dropped, &Fate::Falsified) == Fate::Falsified);
}

#[test]
fn m02_delta_order_flipped() {
    // Loss 10 retains less than loss 3.
    assert!(fate_le(
        &Fate::Atten(Delta::Q(10)),
        &Fate::Atten(Delta::Q(3))
    ));
}

#[test]
fn m03_misbound_not_absorbing() {
    assert!(bond_compose(&Bond::Misbound, &Bond::Intact) == Bond::Misbound);
}

#[test]
fn m04_quality_floor_inverted() {
    let mut dropped = epsilon();
    dropped.q = Fate::Dropped;
    assert!(violations(&floor_q(Fate::Present), &epsilon()).is_empty());
    assert!(violations(&floor_q(Fate::Present), &dropped) == vec!["fate.quality".to_string()]);
}

#[test]
fn m05_dadd_drops_rhs() {
    assert!(dadd(&Delta::Q(2), &Delta::Q(3)) == Delta::Q(5));
}

#[test]
fn m06_merge_compose_max() {
    assert!(merge_compose(&Merge::Single, &Merge::Fused) == Merge::Fused);
}

#[test]
fn m07_a2_reverted() {
    assert!(fate_le(&Fate::Dropped, &Fate::Predicated));
}
