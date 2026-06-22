#!/usr/bin/env python3
# SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
# SPDX-License-Identifier: MPL-2.0
"""The portable tropechecker — a pure function from Trope IR to a verdict.

It reads a Trope IR document (the language-neutral trust boundary; see
``schemas/trope-ir.schema.json`` and ``spec/trope-ir.adoc``), composes the
loss-shape grades over the DAG, and returns ``p-sufficient`` / ``p-insufficient``
against the declared use-model floor, with a witness edge when insufficient.

It MUST NOT parse, import, or execute any source language (HC-1). It is the
shipping/executable core; the Idris2 development in ``src/`` is the verified
reference; the conformance suite ties the two together (calculus §9.3).

This module mirrors the normative grade algebra of ``spec/calculus.adoc``:
  * the three coordinate lattices (fate per field, bond, merge),
  * composition ``▷`` (componentwise; tropical addition on fidelity),
  * the retention order ``⊑`` (componentwise product order),
  * the verdict ``floor(U) ⊑ g`` and the witness edge.

Order convention (stated to remove the one notational ambiguity in the spec):
``⊑`` is the RETENTION order — ``x ⊑ y`` iff ``y`` retains at least as much
particularity as ``x``. ``fuse`` combines its two inputs by the retention-MEET
(the result is "no better than its worse constituent in any coordinate", calculus
§ T-Fuse prose), which is the sound direction.
"""
from __future__ import annotations

import json
import sys
from dataclasses import dataclass
from typing import Optional

# --------------------------------------------------------------------------- #
# Fidelity dimension: N ∪ {∞, ⊤}, as the loss magnitude. Retention DECREASES as
# loss increases. We carry loss magnitude as an ordered token; bigger loss = less
# retention. Tokens: integers (finite), "inf" (total quantified loss), "top"
# (unknown amount — the honest answer for unbounded loss; the absorbing bottom).
# --------------------------------------------------------------------------- #
FIN, INF, TOP = "fin", "inf", "top"


def _delta_key(d):
    """A sort key in INCREASING loss (so larger key = LESS retention)."""
    if d in ("inf",):
        return (1, 0)
    if d in ("top",):
        return (2, 0)
    return (0, int(d))  # finite


def delta_add(a, b):
    """Tropical addition of loss: ⊤ absorbs ∞ absorbs finite (calculus L3)."""
    if a == "top" or b == "top":
        return "top"
    if a == "inf" or b == "inf":
        return "inf"
    return int(a) + int(b)


# --------------------------------------------------------------------------- #
# Grade coordinates as small immutable values.
# --------------------------------------------------------------------------- #
@dataclass(frozen=True)
class Fate:
    k: str                      # Present | Attenuated | Predicated | Dropped | Falsified
    delta: object = None        # for Attenuated
    predicate: Optional[str] = None  # for Predicated

    def __str__(self):
        if self.k == "Attenuated":
            return f"Attenuated({self.delta})"
        if self.k == "Predicated":
            return f"Predicated({self.predicate})"
        return self.k


PRESENT = Fate("Present")
DROPPED = Fate("Dropped")
FALSIFIED = Fate("Falsified")   # deceptive; semantics/detect only


def fate_from_json(o) -> Fate:
    k = o["k"]
    if k == "Attenuated":
        d = o["delta"]
        d = int(d) if isinstance(d, int) or (isinstance(d, str) and d.isdigit()) else d
        if (isinstance(d, int) and d == 0):
            return PRESENT                       # Attenuated(0) = Present (calculus §3.1)
        return Fate("Attenuated", delta=d)
    if k == "Predicated":
        return Fate("Predicated", predicate=o["predicate"])
    return Fate(k)


# Fate retention order: returns True iff `lo ⊑ hi` (hi retains at least as much).
def fate_le(lo: Fate, hi: Fate) -> bool:
    if lo == hi:
        return True
    if lo.k == "Falsified" or hi.k == "Falsified":
        # deceptive value: fails every honest comparison except equality (HC-2c).
        return lo == hi
    # Present is top.
    if hi.k == "Present":
        return True
    if lo.k == "Present":
        return False
    # Attenuated chain, decreasing in delta.
    if lo.k == "Attenuated" and hi.k == "Attenuated":
        return _delta_key(lo.delta) >= _delta_key(hi.delta)  # hi loses ≤ lo
    # Predicated is below every Attenuated, incomparable to Dropped (calculus §3.1).
    if lo.k == "Predicated":
        return hi.k in ("Attenuated", "Present")  # Present handled above
    if hi.k == "Predicated":
        return lo.k == "Predicated"
    # Dropped is below every Attenuated, incomparable to Predicated.
    if lo.k == "Dropped":
        return hi.k in ("Attenuated", "Present")
    if hi.k == "Dropped":
        return lo.k == "Dropped"
    return False


# Fate composition ▷ (apply second to residual of first).
def fate_compose(a: Fate, b: Fate) -> Fate:
    if b == PRESENT:
        return a
    if a == PRESENT:
        return b
    if a.k == "Falsified" or b.k == "Falsified":
        return FALSIFIED                          # deceptive is infectious
    if a.k == "Dropped":
        return DROPPED                            # nothing further from nothing
    if b.k == "Dropped":
        return DROPPED
    if b.k == "Predicated":
        return b                                  # collapse subsumes prior loss
    if a.k == "Predicated":
        # Predicated ▷ Attenuated: the bit has degraded; remains Predicated.
        return a
    # Attenuated ▷ Attenuated: losses add (tropical).
    return Fate("Attenuated", delta=delta_add(a.delta, b.delta))


# Fate retention meet (greatest lower bound): the worse-retaining of two.
def fate_meet(a: Fate, b: Fate) -> Fate:
    if fate_le(a, b):
        return a
    if fate_le(b, a):
        return b
    # incomparable (e.g. Predicated vs Dropped): their common lower bound.
    # Both are below every Attenuated; the only honest lower bound we model is
    # the more-dropped of the two. Conservatively return DROPPED.
    return DROPPED


# --------------------------------------------------------------------------- #
# Bond: Intact ⊐ Withheld ⊐ Severed (chain). Misbound is the deceptive dual of
# Intact (bearer present but false); it fails every honest comparison.
# --------------------------------------------------------------------------- #
_BOND_RANK = {"Intact": 3, "Withheld": 2, "Severed": 1}  # higher = more retention


@dataclass(frozen=True)
class Bond:
    k: str


def bond_le(lo: Bond, hi: Bond) -> bool:
    if lo.k == "Misbound" or hi.k == "Misbound":
        return lo == hi
    return _BOND_RANK[lo.k] <= _BOND_RANK[hi.k]


def bond_compose(a: Bond, b: Bond) -> Bond:
    if a.k == "Misbound" or b.k == "Misbound":
        return Bond("Misbound")
    # meet in the chain, Severed absorbing (calculus §4.1).
    return a if _BOND_RANK[a.k] <= _BOND_RANK[b.k] else b


def bond_meet(a: Bond, b: Bond) -> Bond:
    if a.k == "Misbound" or b.k == "Misbound":
        return Bond("Misbound")
    return a if _BOND_RANK[a.k] <= _BOND_RANK[b.k] else b


# --------------------------------------------------------------------------- #
# Merge: Single ⊐ Fused(τ) ⊐ Conflated (chain). Conflated is deceptive/infectious.
# Tags are ignored by the order (recoverable plurality is what matters).
# --------------------------------------------------------------------------- #
_MERGE_RANK = {"Single": 3, "Fused": 2, "Conflated": 1}


@dataclass(frozen=True)
class Merge:
    k: str
    tau: Optional[str] = None

    def __str__(self):
        return f"Fused({self.tau})" if self.k == "Fused" else self.k


def merge_le(lo: Merge, hi: Merge) -> bool:
    if lo.k == "Conflated" or hi.k == "Conflated":
        return lo.k == "Conflated" and hi.k == "Conflated"
    return _MERGE_RANK[lo.k] <= _MERGE_RANK[hi.k]


def merge_compose(a: Merge, b: Merge) -> Merge:
    if a.k == "Conflated" or b.k == "Conflated":
        return Merge("Conflated")                 # L5: conflation infectiousness
    if a.k == "Fused" and b.k == "Fused":
        return Merge("Fused", tau=f"({a.tau}⊗{b.tau})")
    return a if _MERGE_RANK[a.k] <= _MERGE_RANK[b.k] else b


def merge_meet(a: Merge, b: Merge) -> Merge:
    if a.k == "Conflated" or b.k == "Conflated":
        return Merge("Conflated")
    return a if _MERGE_RANK[a.k] <= _MERGE_RANK[b.k] else b


# --------------------------------------------------------------------------- #
# Grade = (fate: field→Fate, bond, merge).
# --------------------------------------------------------------------------- #
FIELDS = ("quality", "bearer", "context", "record")


@dataclass(frozen=True)
class Grade:
    fate: tuple            # ((field, Fate), ...) over all four fields
    bond: Bond
    merge: Merge

    def fate_of(self, f) -> Fate:
        return dict(self.fate)[f]


EPSILON = Grade(
    fate=tuple((f, PRESENT) for f in FIELDS),
    bond=Bond("Intact"),
    merge=Merge("Single"),
)


def grade_from_json(o) -> Grade:
    fate = tuple((f, fate_from_json(o["fate"][f])) for f in FIELDS)
    bond = Bond(o["bond"]["k"])
    m = o["merge"]
    merge = Merge(m["k"], tau=m.get("tau"))
    return Grade(fate=fate, bond=bond, merge=merge)


def grade_compose(a: Grade, b: Grade) -> Grade:
    fate = tuple((f, fate_compose(a.fate_of(f), b.fate_of(f))) for f in FIELDS)
    return Grade(fate=fate, bond=bond_compose(a.bond, b.bond),
                 merge=merge_compose(a.merge, b.merge))


def grade_meet(a: Grade, b: Grade) -> Grade:
    fate = tuple((f, fate_meet(a.fate_of(f), b.fate_of(f))) for f in FIELDS)
    return Grade(fate=fate, bond=bond_meet(a.bond, b.bond),
                 merge=merge_meet(a.merge, b.merge))


# --------------------------------------------------------------------------- #
# Floor (partial grade) and the per-coordinate subsumption with diagnostics.
# --------------------------------------------------------------------------- #
def floor_violations(floor: dict, g: Grade) -> list:
    """Return the list of coordinates where floor demands more than g retains.

    Each item: a dotted coordinate name, e.g. "fate.quality", "bond", "merge".
    Empty list ⟺ floor(U) ⊑ g ⟺ p-sufficient.
    """
    bad = []
    if "fate" in floor:
        for f in FIELDS:
            if f in floor["fate"]:
                demand = fate_from_json(floor["fate"][f])
                if not fate_le(demand, g.fate_of(f)):
                    bad.append(f"fate.{f}")
    if "bond" in floor:
        if not bond_le(Bond(floor["bond"]["k"]), g.bond):
            bad.append("bond")
    if "merge" in floor:
        m = floor["merge"]
        if not merge_le(Merge(m["k"], tau=m.get("tau")), g.merge):
            bad.append("merge")
    return bad


# --------------------------------------------------------------------------- #
# The DAG: accumulate grades, decide the verdict, locate the witness.
# --------------------------------------------------------------------------- #
class IRError(Exception):
    pass


def _topo_order(nodes, edges):
    """Return edge ids in a topological order (producers before consumers)."""
    producer = {e["output"]: e["id"] for e in edges}
    by_id = {e["id"]: e for e in edges}
    seen, order = set(), []

    def visit(eid):
        if eid in seen:
            return
        seen.add(eid)
        for src in by_id[eid]["inputs"]:
            if src in producer:
                visit(producer[src])
        order.append(eid)

    for e in edges:
        visit(e["id"])
    return order, by_id, producer


def check(doc: dict) -> dict:
    """Return a verdict object: {verdict, witness?, failing_coordinates?}."""
    nodes = {n["id"]: n for n in doc["nodes"]}
    edges = doc["edges"]
    um = doc["use_model"]
    floor = um["floor"]
    out = um["output"]
    if out not in nodes:
        raise IRError(f"use_model.output '{out}' is not a node")

    order, by_id, producer = _topo_order(nodes, edges)

    acc: dict = {}

    def accumulate(node_id) -> Grade:
        if node_id in acc:
            return acc[node_id]
        eid = producer.get(node_id)
        if eid is None:
            acc[node_id] = EPSILON                 # root property-instance
            return EPSILON
        e = by_id[eid]
        ins = [accumulate(s) for s in e["inputs"]]
        eg = grade_from_json(e["grade"])
        if len(ins) == 1:
            g = grade_compose(ins[0], eg)
        else:                                      # fuse: meet of inputs ▷ label
            base = ins[0]
            for other in ins[1:]:
                base = grade_meet(base, other)
            g = grade_compose(base, eg)
        acc[node_id] = g
        return g

    final = accumulate(out)
    bad = floor_violations(floor, final)
    if not bad:
        return {"verdict": "p-sufficient"}

    # Witness: the topologically-first edge whose output's accumulated grade
    # first drops below the floor in a failing coordinate (calculus §6.2).
    witness = None
    witness_coord = None
    for eid in order:
        e = by_id[eid]
        if e["output"] not in acc:               # not on the path to `out`
            continue
        v = floor_violations(floor, acc[e["output"]])
        hit = [c for c in v if c in bad]
        if hit:
            witness, witness_coord = eid, hit[0]
            break

    return {
        "verdict": "p-insufficient",
        "failing_coordinates": bad,
        "witness": witness,
        "witness_coordinate": witness_coord,
    }


def main(argv) -> int:
    if len(argv) != 2:
        print("usage: tropecheck.py <ir.json>", file=sys.stderr)
        return 2
    doc = json.loads(open(argv[1], encoding="utf-8").read())
    result = check(doc)
    print(json.dumps(result, indent=2, ensure_ascii=False))
    return 0 if result["verdict"] == "p-sufficient" else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
