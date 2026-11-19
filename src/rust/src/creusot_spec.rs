// SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0
//
// Creusot logical model and laws for the Rust fast core.
//
// Compiled ONLY under `cfg(creusot)` (see the top of lib.rs). An ordinary build
// never sees this file.
//
// Layout:
//   1. The model types. `Delta` and `Fate` carry an `i64`, so their deep model is a
//      mirror type over the unbounded `Int`. `Bond` and `Merge` are their own model.
//   2. Transcriptions of the Rust functions (`*_m`). Each program function in lib.rs
//      carries `ensures(result.deep_model() == f_m(..))`, so Creusot proves the Rust
//      code equal to the transcription.
//   3. Transcriptions of the Agda reference order (`agda_*`), copied clause by
//      clause from verification/proofs/agda/theorem-b/TB/Order.agda.
//   4. The laws, as lemmas over the transcriptions: L1, L2, L3, L4, L5, L6, A2,
//      preorder, honest closure, wf preservation, meet as glb on the honest
//      fragment, and the honest correspondence with Agda.
//
// Divergence carried here, not fixed (hub ruling, 19 Nov): Agda and Idris2 put each
// deceptive bottom (Falsified, Misbound, Conflated) at the BOTTOM of the order. The
// Rust order makes it comparable only with itself. The correspondence lemmas are
// therefore stated on the honest fragment. The unrestricted correspondence is a
// planted control that Creusot must refuse (verification/creusot/controls).

use crate::*;
use creusot_std::prelude::*;

// ───────────────────────────── 1. model types ─────────────────────────────

/// Deep model of `Delta`: the finite loss is an unbounded integer.
pub enum DeltaM {
    Q(Int),
    Inf,
    Top,
}

/// Deep model of `Fate`.
pub enum FateM {
    Present,
    Atten(DeltaM),
    Predicated,
    Dropped,
    Falsified,
}

/// Deep model of `Grade`.
pub struct GradeM {
    pub q: FateM,
    pub b: FateM,
    pub c: FateM,
    pub r: FateM,
    pub bond: Bond,
    pub merge: Merge,
}

// ───────────────────────── 2. transcriptions of the Rust code ─────────────────────────

/// First component of `dkey`.
#[logic(open)]
pub fn dtag(d: DeltaM) -> Int {
    match d {
        DeltaM::Q(_) => 0,
        DeltaM::Inf => 1,
        DeltaM::Top => 2,
    }
}

/// Second component of `dkey`.
#[logic(open)]
pub fn dval(d: DeltaM) -> Int {
    match d {
        DeltaM::Q(n) => n,
        DeltaM::Inf => 0,
        DeltaM::Top => 0,
    }
}

/// The Rust delta order used inside `fate_le`: `a` retains at most as much as `b`
/// iff `dkey(a) >= dkey(b)` lexicographically.
#[logic(open)]
pub fn dle_m(a: DeltaM, b: DeltaM) -> bool {
    dtag(a) > dtag(b) || (dtag(a) == dtag(b) && dval(a) >= dval(b))
}

/// `dadd`, over unbounded integers.
#[logic(open)]
pub fn dadd_m(a: DeltaM, b: DeltaM) -> DeltaM {
    match a {
        DeltaM::Top => DeltaM::Top,
        DeltaM::Inf => match b {
            DeltaM::Top => DeltaM::Top,
            _ => DeltaM::Inf,
        },
        DeltaM::Q(x) => match b {
            DeltaM::Top => DeltaM::Top,
            DeltaM::Inf => DeltaM::Inf,
            DeltaM::Q(y) => DeltaM::Q(x + y),
        },
    }
}

/// Owner ruling (1): i64 overflow is a precondition proved at callers, never a
/// wrapping behaviour. This is that precondition for `dadd`.
#[logic(open)]
pub fn d_no_ovf(a: DeltaM, b: DeltaM) -> bool {
    match a {
        DeltaM::Q(x) => match b {
            DeltaM::Q(y) => pearlite! { i64::MIN@ <= x + y && x + y <= i64::MAX@ },
            _ => true,
        },
        _ => true,
    }
}

/// The overflow precondition lifted to `fate_compose` (only Atten·Atten adds).
#[logic(open)]
pub fn f_no_ovf(a: FateM, b: FateM) -> bool {
    match a {
        FateM::Atten(d1) => match b {
            FateM::Atten(d2) => d_no_ovf(d1, d2),
            _ => true,
        },
        _ => true,
    }
}

/// The overflow precondition lifted to `grade_compose`.
#[logic(open)]
pub fn g_no_ovf(a: GradeM, b: GradeM) -> bool {
    f_no_ovf(a.q, b.q) && f_no_ovf(a.b, b.b) && f_no_ovf(a.c, b.c) && f_no_ovf(a.r, b.r)
}

/// `fate_le`, clause by clause.
#[logic(open)]
pub fn fate_le_m(lo: FateM, hi: FateM) -> bool {
    if lo == hi {
        true
    } else if lo == FateM::Falsified || hi == FateM::Falsified {
        false
    } else if hi == FateM::Present {
        true
    } else if lo == FateM::Present {
        false
    } else {
        match lo {
            FateM::Atten(a) => match hi {
                FateM::Atten(b) => dle_m(a, b),
                _ => false,
            },
            FateM::Predicated => match hi {
                FateM::Atten(_) => true,
                _ => false,
            },
            FateM::Dropped => match hi {
                FateM::Atten(_) => true,
                FateM::Predicated => true,
                _ => false,
            },
            _ => false,
        }
    }
}

/// `fate_compose`, clause by clause (A1: the lie survives the drop).
#[logic(open)]
pub fn fate_compose_m(a: FateM, b: FateM) -> FateM {
    match a {
        FateM::Falsified => FateM::Falsified,
        FateM::Present => b,
        FateM::Dropped => match b {
            FateM::Falsified => FateM::Falsified,
            _ => FateM::Dropped,
        },
        FateM::Predicated => match b {
            FateM::Falsified => FateM::Falsified,
            FateM::Dropped => FateM::Dropped,
            _ => FateM::Predicated,
        },
        FateM::Atten(d1) => match b {
            FateM::Falsified => FateM::Falsified,
            FateM::Dropped => FateM::Dropped,
            FateM::Present => FateM::Atten(d1),
            FateM::Atten(d2) => FateM::Atten(dadd_m(d1, d2)),
            FateM::Predicated => FateM::Predicated,
        },
    }
}

/// `fate_meet`: the smaller of two comparable fates, else `Dropped`.
#[logic(open)]
pub fn fate_meet_m(a: FateM, b: FateM) -> FateM {
    if fate_le_m(a, b) {
        a
    } else if fate_le_m(b, a) {
        b
    } else {
        FateM::Dropped
    }
}

/// `bond_rank`.
#[logic(open)]
pub fn brank(b: Bond) -> Int {
    match b {
        Bond::Intact => 3,
        Bond::Withheld => 2,
        Bond::Severed => 1,
        Bond::Misbound => 0,
    }
}

/// `bond_le`.
#[logic(open)]
pub fn bond_le_m(lo: Bond, hi: Bond) -> bool {
    if lo == Bond::Misbound || hi == Bond::Misbound {
        lo == hi
    } else {
        brank(lo) <= brank(hi)
    }
}

/// `bond_compose` (and `bond_meet`, which is the same function).
#[logic(open)]
pub fn bond_compose_m(a: Bond, b: Bond) -> Bond {
    if a == Bond::Misbound || b == Bond::Misbound {
        Bond::Misbound
    } else if brank(a) <= brank(b) {
        a
    } else {
        b
    }
}

/// `merge_rank`.
#[logic(open)]
pub fn mrank(m: Merge) -> Int {
    match m {
        Merge::Single => 3,
        Merge::Fused => 2,
        Merge::Conflated => 1,
    }
}

/// `merge_le`.
#[logic(open)]
pub fn merge_le_m(lo: Merge, hi: Merge) -> bool {
    if lo == Merge::Conflated || hi == Merge::Conflated {
        lo == hi
    } else {
        mrank(lo) <= mrank(hi)
    }
}

/// `merge_compose` (and `merge_meet`).
#[logic(open)]
pub fn merge_compose_m(a: Merge, b: Merge) -> Merge {
    if a == Merge::Conflated || b == Merge::Conflated {
        Merge::Conflated
    } else if mrank(a) <= mrank(b) {
        a
    } else {
        b
    }
}

/// `epsilon()`.
#[logic(open)]
pub fn eps_m() -> GradeM {
    GradeM {
        q: FateM::Present,
        b: FateM::Present,
        c: FateM::Present,
        r: FateM::Present,
        bond: Bond::Intact,
        merge: Merge::Single,
    }
}

/// `grade_compose`.
#[logic(open)]
pub fn grade_compose_m(a: GradeM, b: GradeM) -> GradeM {
    GradeM {
        q: fate_compose_m(a.q, b.q),
        b: fate_compose_m(a.b, b.b),
        c: fate_compose_m(a.c, b.c),
        r: fate_compose_m(a.r, b.r),
        bond: bond_compose_m(a.bond, b.bond),
        merge: merge_compose_m(a.merge, b.merge),
    }
}

/// `grade_meet`.
#[logic(open)]
pub fn grade_meet_m(a: GradeM, b: GradeM) -> GradeM {
    GradeM {
        q: fate_meet_m(a.q, b.q),
        b: fate_meet_m(a.b, b.b),
        c: fate_meet_m(a.c, b.c),
        r: fate_meet_m(a.r, b.r),
        bond: bond_compose_m(a.bond, b.bond),
        merge: merge_compose_m(a.merge, b.merge),
    }
}

/// `grade_le`: the componentwise product order.
#[logic(open)]
pub fn grade_le_m(lo: GradeM, hi: GradeM) -> bool {
    fate_le_m(lo.q, hi.q)
        && fate_le_m(lo.b, hi.b)
        && fate_le_m(lo.c, hi.c)
        && fate_le_m(lo.r, hi.r)
        && bond_le_m(lo.bond, hi.bond)
        && merge_le_m(lo.merge, hi.merge)
}

/// One optional floor coordinate: absent imposes nothing.
#[logic(open)]
pub fn opt_fate_le(fl: Option<Fate>, g: FateM) -> bool {
    match fl {
        None => true,
        Some(d) => fate_le_m(d.deep_model(), g),
    }
}

/// The floor order checked by `violations`: every coordinate the floor sets is met.
#[logic(open)]
pub fn floor_le_m(fl: Floor, g: GradeM) -> bool {
    opt_fate_le(fl.q, g.q)
        && opt_fate_le(fl.b, g.b)
        && opt_fate_le(fl.c, g.c)
        && opt_fate_le(fl.r, g.r)
        && match fl.bond {
            None => true,
            Some(d) => bond_le_m(d, g.bond),
        }
        && match fl.merge {
            None => true,
            Some(d) => merge_le_m(d, g.merge),
        }
}

// ───────────────────────── honesty and well-formedness ─────────────────────────

#[logic(open)]
pub fn honest_f(f: FateM) -> bool {
    f != FateM::Falsified
}

#[logic(open)]
pub fn honest_g(g: GradeM) -> bool {
    honest_f(g.q)
        && honest_f(g.b)
        && honest_f(g.c)
        && honest_f(g.r)
        && g.bond != Bond::Misbound
        && g.merge != Merge::Conflated
}

/// Finite losses are non-negative (the decoder admits only `n >= 0`).
#[logic(open)]
pub fn nonneg_f(f: FateM) -> bool {
    match f {
        FateM::Atten(DeltaM::Q(n)) => n >= 0,
        _ => true,
    }
}

/// A3 normal form: `Atten(Q 0)` never occurs (the decoder rewrites it to `Present`).
#[logic(open)]
pub fn normal_f(f: FateM) -> bool {
    match f {
        FateM::Atten(DeltaM::Q(n)) => n != 0,
        _ => true,
    }
}

#[logic(open)]
pub fn wf_f(f: FateM) -> bool {
    nonneg_f(f) && normal_f(f)
}

#[logic(open)]
pub fn wf_g(g: GradeM) -> bool {
    wf_f(g.q) && wf_f(g.b) && wf_f(g.c) && wf_f(g.r)
}

// ───────────────────────── 3. the Agda reference order ─────────────────────────
// Copied from TB/Order.agda (dLte, fateLte, bondLte, mergeLte).
// Agda's Δ is `Q ℕ | total | unknown`; Rust's Inf is `total`, Top is `unknown`.

#[logic(open)]
pub fn agda_dlte(a: DeltaM, b: DeltaM) -> bool {
    match a {
        DeltaM::Top => true,
        DeltaM::Q(x) => match b {
            DeltaM::Q(y) => y <= x,
            _ => false,
        },
        DeltaM::Inf => match b {
            DeltaM::Top => false,
            _ => true,
        },
    }
}

#[logic(open)]
pub fn agda_fate_le(a: FateM, b: FateM) -> bool {
    match a {
        FateM::Falsified => true,
        FateM::Present => b == FateM::Present,
        FateM::Atten(x) => match b {
            FateM::Present => true,
            FateM::Atten(y) => agda_dlte(x, y),
            _ => false,
        },
        FateM::Predicated => match b {
            FateM::Present => true,
            FateM::Atten(_) => true,
            FateM::Predicated => true,
            _ => false,
        },
        FateM::Dropped => b != FateM::Falsified,
    }
}

#[logic(open)]
pub fn agda_bond_le(a: Bond, b: Bond) -> bool {
    match a {
        Bond::Misbound => true,
        _ => b != Bond::Misbound && brank(a) <= brank(b),
    }
}

#[logic(open)]
pub fn agda_merge_le(a: Merge, b: Merge) -> bool {
    match a {
        Merge::Conflated => true,
        _ => b != Merge::Conflated && mrank(a) <= mrank(b),
    }
}

// ───────────────────────────────── 4. laws ─────────────────────────────────
// Each lemma is a logic function whose contract is the law. Bodies are empty
// unless a case split is needed to guide the solvers.

// L1 associativity.
#[logic(open)]
#[ensures(dadd_m(dadd_m(a, b), c) == dadd_m(a, dadd_m(b, c)))]
pub fn l1_dadd_assoc(a: DeltaM, b: DeltaM, c: DeltaM) {}

#[logic(open)]
#[ensures(fate_compose_m(fate_compose_m(a, b), c) == fate_compose_m(a, fate_compose_m(b, c)))]
pub fn l1_fate_assoc(a: FateM, b: FateM, c: FateM) {
    match a {
        FateM::Atten(x) => match b {
            FateM::Atten(y) => match c {
                FateM::Atten(z) => l1_dadd_assoc(x, y, z),
                _ => (),
            },
            _ => (),
        },
        _ => (),
    }
}

#[logic(open)]
#[ensures(bond_compose_m(bond_compose_m(a, b), c) == bond_compose_m(a, bond_compose_m(b, c)))]
pub fn l1_bond_assoc(a: Bond, b: Bond, c: Bond) {}

#[logic(open)]
#[ensures(merge_compose_m(merge_compose_m(a, b), c) == merge_compose_m(a, merge_compose_m(b, c)))]
pub fn l1_merge_assoc(a: Merge, b: Merge, c: Merge) {}

#[logic(open)]
#[ensures(grade_compose_m(grade_compose_m(a, b), c) == grade_compose_m(a, grade_compose_m(b, c)))]
pub fn l1_grade_assoc(a: GradeM, b: GradeM, c: GradeM) {
    l1_fate_assoc(a.q, b.q, c.q);
    l1_fate_assoc(a.b, b.b, c.b);
    l1_fate_assoc(a.c, b.c, c.c);
    l1_fate_assoc(a.r, b.r, c.r);
    l1_bond_assoc(a.bond, b.bond, c.bond);
    l1_merge_assoc(a.merge, b.merge, c.merge);
}

// L2 unit.
#[logic(open)]
#[ensures(fate_compose_m(FateM::Present, a) == a && fate_compose_m(a, FateM::Present) == a)]
pub fn l2_fate_unit(a: FateM) {}

#[logic(open)]
#[ensures(bond_compose_m(Bond::Intact, a) == a && bond_compose_m(a, Bond::Intact) == a)]
pub fn l2_bond_unit(a: Bond) {}

#[logic(open)]
#[ensures(merge_compose_m(Merge::Single, a) == a && merge_compose_m(a, Merge::Single) == a)]
pub fn l2_merge_unit(a: Merge) {}

#[logic(open)]
#[ensures(grade_compose_m(eps_m(), a) == a && grade_compose_m(a, eps_m()) == a)]
pub fn l2_grade_unit(a: GradeM) {
    l2_fate_unit(a.q);
    l2_fate_unit(a.b);
    l2_fate_unit(a.c);
    l2_fate_unit(a.r);
    l2_bond_unit(a.bond);
    l2_merge_unit(a.merge);
}

// L6 commutativity.
#[logic(open)]
#[ensures(dadd_m(a, b) == dadd_m(b, a))]
pub fn l6_dadd_comm(a: DeltaM, b: DeltaM) {}

#[logic(open)]
#[ensures(fate_compose_m(a, b) == fate_compose_m(b, a))]
pub fn l6_fate_comm(a: FateM, b: FateM) {
    match a {
        FateM::Atten(x) => match b {
            FateM::Atten(y) => l6_dadd_comm(x, y),
            _ => (),
        },
        _ => (),
    }
}

#[logic(open)]
#[ensures(bond_compose_m(a, b) == bond_compose_m(b, a))]
pub fn l6_bond_comm(a: Bond, b: Bond) {}

#[logic(open)]
#[ensures(merge_compose_m(a, b) == merge_compose_m(b, a))]
pub fn l6_merge_comm(a: Merge, b: Merge) {}

#[logic(open)]
#[ensures(grade_compose_m(a, b) == grade_compose_m(b, a))]
pub fn l6_grade_comm(a: GradeM, b: GradeM) {
    l6_fate_comm(a.q, b.q);
    l6_fate_comm(a.b, b.b);
    l6_fate_comm(a.c, b.c);
    l6_fate_comm(a.r, b.r);
    l6_bond_comm(a.bond, b.bond);
    l6_merge_comm(a.merge, b.merge);
}

// L3 bottom absorption, two-sided, for every deceptive bottom.
#[logic(open)]
#[ensures(fate_compose_m(FateM::Falsified, a) == FateM::Falsified)]
#[ensures(fate_compose_m(a, FateM::Falsified) == FateM::Falsified)]
pub fn l3_falsified_absorbs(a: FateM) {}

#[logic(open)]
#[ensures(bond_compose_m(Bond::Misbound, a) == Bond::Misbound)]
#[ensures(bond_compose_m(a, Bond::Misbound) == Bond::Misbound)]
pub fn l3_misbound_absorbs(a: Bond) {}

#[logic(open)]
#[ensures(merge_compose_m(Merge::Conflated, a) == Merge::Conflated)]
#[ensures(merge_compose_m(a, Merge::Conflated) == Merge::Conflated)]
pub fn l3_conflated_absorbs(a: Merge) {}

/// Fidelity: `Unknown` (Rust `Top`) is a two-sided zero; `Total` (Rust `Inf`)
/// absorbs every finite loss.
#[logic(open)]
#[ensures(dadd_m(DeltaM::Top, a) == DeltaM::Top && dadd_m(a, DeltaM::Top) == DeltaM::Top)]
#[ensures(a != DeltaM::Top ==> dadd_m(DeltaM::Inf, a) == DeltaM::Inf && dadd_m(a, DeltaM::Inf) == DeltaM::Inf)]
pub fn l3_fidelity_absorbs(a: DeltaM) {}

// L5 deception infectiousness: a deceptive operand makes the result deceptive.
#[logic(open)]
#[ensures(!honest_f(a) ==> !honest_f(fate_compose_m(a, b)) && !honest_f(fate_compose_m(b, a)))]
pub fn l5_fate(a: FateM, b: FateM) {}

#[logic(open)]
#[ensures(!honest_g(a) ==> !honest_g(grade_compose_m(a, b)) && !honest_g(grade_compose_m(b, a)))]
pub fn l5_grade(a: GradeM, b: GradeM) {}

// Honest closure (the closure half of Honest Generation).
#[logic(open)]
#[requires(honest_g(a) && honest_g(b))]
#[ensures(honest_g(grade_compose_m(a, b)))]
#[ensures(honest_g(grade_meet_m(a, b)))]
pub fn honest_closed(a: GradeM, b: GradeM) {}

// wf (non-negative, A3-normal) is preserved by composition and meet.
#[logic(open)]
#[requires(wf_f(a) && wf_f(b))]
#[ensures(wf_f(fate_compose_m(a, b)))]
#[ensures(wf_f(fate_meet_m(a, b)))]
pub fn wf_fate_closed(a: FateM, b: FateM) {}

#[logic(open)]
#[requires(wf_g(a) && wf_g(b))]
#[ensures(wf_g(grade_compose_m(a, b)))]
#[ensures(wf_g(grade_meet_m(a, b)))]
pub fn wf_grade_closed(a: GradeM, b: GradeM) {
    wf_fate_closed(a.q, b.q);
    wf_fate_closed(a.b, b.b);
    wf_fate_closed(a.c, b.c);
    wf_fate_closed(a.r, b.r);
}

#[logic(open)]
#[ensures(wf_g(eps_m()) && honest_g(eps_m()))]
pub fn eps_honest_wf() {}

// The order: reflexive, transitive, antisymmetric.
#[logic(open)]
#[ensures(fate_le_m(a, a) && bond_le_m(b, b) && merge_le_m(m, m))]
pub fn order_refl(a: FateM, b: Bond, m: Merge) {}

#[logic(open)]
#[requires(fate_le_m(a, b) && fate_le_m(b, c))]
#[ensures(fate_le_m(a, c))]
pub fn fate_trans(a: FateM, b: FateM, c: FateM) {}

#[logic(open)]
#[requires(fate_le_m(a, b) && fate_le_m(b, a))]
#[ensures(a == b)]
pub fn fate_antisym(a: FateM, b: FateM) {}

#[logic(open)]
#[requires(bond_le_m(a, b) && bond_le_m(b, c))]
#[ensures(bond_le_m(a, c))]
pub fn bond_trans(a: Bond, b: Bond, c: Bond) {}

#[logic(open)]
#[requires(merge_le_m(a, b) && merge_le_m(b, c))]
#[ensures(merge_le_m(a, c))]
pub fn merge_trans(a: Merge, b: Merge, c: Merge) {}

#[logic(open)]
#[ensures(grade_le_m(a, a))]
pub fn grade_refl(a: GradeM) {
    order_refl(a.q, a.bond, a.merge);
    order_refl(a.b, a.bond, a.merge);
    order_refl(a.c, a.bond, a.merge);
    order_refl(a.r, a.bond, a.merge);
}

#[logic(open)]
#[requires(grade_le_m(a, b) && grade_le_m(b, c))]
#[ensures(grade_le_m(a, c))]
pub fn grade_trans(a: GradeM, b: GradeM, c: GradeM) {
    fate_trans(a.q, b.q, c.q);
    fate_trans(a.b, b.b, c.b);
    fate_trans(a.c, b.c, c.c);
    fate_trans(a.r, b.r, c.r);
    bond_trans(a.bond, b.bond, c.bond);
    merge_trans(a.merge, b.merge, c.merge);
}

// A2: fate is a chain on the honest fragment, and Dropped ⊑ Predicated, not back.
#[logic(open)]
#[ensures(fate_le_m(FateM::Dropped, FateM::Predicated))]
#[ensures(!fate_le_m(FateM::Predicated, FateM::Dropped))]
pub fn a2_dropped_le_predicated() {}

#[logic(open)]
#[requires(honest_f(a) && honest_f(b))]
#[ensures(fate_le_m(a, b) || fate_le_m(b, a))]
pub fn a2_fate_total_on_honest(a: FateM, b: FateM) {}

// L4 monotonicity of composition in both arguments, under non-negative losses.
// (Non-negativity is needed: with Atten(Q -1) ⊑ Present, composing both with
// Atten(Q 1) gives Atten(Q 0) ⋢ Atten(Q 1).)
#[logic(open)]
#[requires(nonneg_f(a) && nonneg_f(b) && nonneg_f(c))]
#[requires(fate_le_m(a, b))]
#[ensures(fate_le_m(fate_compose_m(a, c), fate_compose_m(b, c)))]
#[ensures(fate_le_m(fate_compose_m(c, a), fate_compose_m(c, b)))]
pub fn l4_fate_mono(a: FateM, b: FateM, c: FateM) {
    l6_fate_comm(a, c);
    l6_fate_comm(b, c);
}

#[logic(open)]
#[requires(bond_le_m(a, b))]
#[ensures(bond_le_m(bond_compose_m(a, c), bond_compose_m(b, c)))]
#[ensures(bond_le_m(bond_compose_m(c, a), bond_compose_m(c, b)))]
pub fn l4_bond_mono(a: Bond, b: Bond, c: Bond) {}

#[logic(open)]
#[requires(merge_le_m(a, b))]
#[ensures(merge_le_m(merge_compose_m(a, c), merge_compose_m(b, c)))]
#[ensures(merge_le_m(merge_compose_m(c, a), merge_compose_m(c, b)))]
pub fn l4_merge_mono(a: Merge, b: Merge, c: Merge) {}

/// L4 at grade level: the lifting spec §7's Knaster–Tarski argument uses, which
/// PROOF-STATUS records as not mechanised in Idris2.
#[logic(open)]
#[requires(wf_g(a) && wf_g(b) && wf_g(c))]
#[requires(grade_le_m(a, b))]
#[ensures(grade_le_m(grade_compose_m(a, c), grade_compose_m(b, c)))]
#[ensures(grade_le_m(grade_compose_m(c, a), grade_compose_m(c, b)))]
pub fn l4_grade_mono(a: GradeM, b: GradeM, c: GradeM) {
    l4_fate_mono(a.q, b.q, c.q);
    l4_fate_mono(a.b, b.b, c.b);
    l4_fate_mono(a.c, b.c, c.c);
    l4_fate_mono(a.r, b.r, c.r);
    l4_bond_mono(a.bond, b.bond, c.bond);
    l4_merge_mono(a.merge, b.merge, c.merge);
}

// Meet is the greatest lower bound on the honest fragment.
#[logic(open)]
#[requires(honest_f(a) && honest_f(b))]
#[ensures(fate_le_m(fate_meet_m(a, b), a) && fate_le_m(fate_meet_m(a, b), b))]
#[ensures(fate_le_m(c, a) && fate_le_m(c, b) ==> fate_le_m(c, fate_meet_m(a, b)))]
pub fn fate_meet_glb(a: FateM, b: FateM, c: FateM) {
    a2_fate_total_on_honest(a, b);
}

#[logic(open)]
#[requires(a != Bond::Misbound && b != Bond::Misbound)]
#[ensures(bond_le_m(bond_compose_m(a, b), a) && bond_le_m(bond_compose_m(a, b), b))]
#[ensures(bond_le_m(c, a) && bond_le_m(c, b) ==> bond_le_m(c, bond_compose_m(a, b)))]
pub fn bond_meet_glb(a: Bond, b: Bond, c: Bond) {}

#[logic(open)]
#[requires(a != Merge::Conflated && b != Merge::Conflated)]
#[ensures(merge_le_m(merge_compose_m(a, b), a) && merge_le_m(merge_compose_m(a, b), b))]
#[ensures(merge_le_m(c, a) && merge_le_m(c, b) ==> merge_le_m(c, merge_compose_m(a, b)))]
pub fn merge_meet_glb(a: Merge, b: Merge, c: Merge) {}

#[logic(open)]
#[requires(honest_g(a) && honest_g(b))]
#[ensures(grade_le_m(grade_meet_m(a, b), a) && grade_le_m(grade_meet_m(a, b), b))]
#[ensures(grade_le_m(c, a) && grade_le_m(c, b) ==> grade_le_m(c, grade_meet_m(a, b)))]
pub fn grade_meet_glb(a: GradeM, b: GradeM, c: GradeM) {
    fate_meet_glb(a.q, b.q, c.q);
    fate_meet_glb(a.b, b.b, c.b);
    fate_meet_glb(a.c, b.c, c.c);
    fate_meet_glb(a.r, b.r, c.r);
    bond_meet_glb(a.bond, b.bond, c.bond);
    merge_meet_glb(a.merge, b.merge, c.merge);
}

// Correspondence with the Agda reference order.
// The delta order agrees everywhere; fate, bond and merge agree on the honest
// fragment. Off it they disagree (see the header): that is a planted control.
#[logic(open)]
#[ensures(dle_m(a, b) == agda_dlte(a, b))]
pub fn corr_delta(a: DeltaM, b: DeltaM) {}

#[logic(open)]
#[requires(honest_f(a) && honest_f(b))]
#[ensures(fate_le_m(a, b) == agda_fate_le(a, b))]
pub fn corr_fate_honest(a: FateM, b: FateM) {
    match a {
        FateM::Atten(x) => match b {
            FateM::Atten(y) => corr_delta(x, y),
            _ => (),
        },
        _ => (),
    }
}

#[logic(open)]
#[requires(a != Bond::Misbound && b != Bond::Misbound)]
#[ensures(bond_le_m(a, b) == agda_bond_le(a, b))]
pub fn corr_bond_honest(a: Bond, b: Bond) {}

#[logic(open)]
#[requires(a != Merge::Conflated && b != Merge::Conflated)]
#[ensures(merge_le_m(a, b) == agda_merge_le(a, b))]
pub fn corr_merge_honest(a: Merge, b: Merge) {}

// Verdict soundness (Idris2 Trope.Soundness.verdictSound and subSound): a floor
// met by g, with g ⊑ ρ, is met by ρ.
#[logic(open)]
#[requires(floor_le_m(fl, g) && grade_le_m(g, rho))]
#[ensures(floor_le_m(fl, rho))]
pub fn verdict_sound(fl: Floor, g: GradeM, rho: GradeM) {
    match fl.q {
        Some(d) => fate_trans(d.deep_model(), g.q, rho.q),
        None => (),
    }
    match fl.b {
        Some(d) => fate_trans(d.deep_model(), g.b, rho.b),
        None => (),
    }
    match fl.c {
        Some(d) => fate_trans(d.deep_model(), g.c, rho.c),
        None => (),
    }
    match fl.r {
        Some(d) => fate_trans(d.deep_model(), g.r, rho.r),
        None => (),
    }
    match fl.bond {
        Some(d) => bond_trans(d, g.bond, rho.bond),
        None => (),
    }
    match fl.merge {
        Some(d) => merge_trans(d, g.merge, rho.merge),
        None => (),
    }
}
