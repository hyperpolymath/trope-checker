#!/usr/bin/env python3
# SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
# SPDX-License-Identifier: MPL-2.0
"""Regenerate the conformance corpus (fixtures + cases.json + schema-invalid).

Run from anywhere: it locates the repo root from this file's path. Every positive
fixture is verified against the reference executable checker (src/checker), so a
regeneration that drifts from the algebra fails loudly. Re-run after any change to
the calculus or the checker:  python3 tests/conformance/build_fixtures.py
"""
import json, pathlib, sys

REPO = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "src" / "checker"))
import tropecheck as tc  # noqa: E402

FIX = REPO / "tests" / "conformance" / "fixtures"
INV = REPO / "tests" / "conformance" / "schema-invalid"
FIX.mkdir(parents=True, exist_ok=True)
INV.mkdir(parents=True, exist_ok=True)

SPDX = ("SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) "
        "<j.d.a.jewell@open.ac.uk>. SPDX-License-Identifier: MPL-2.0")

# ---- grade JSON builders ----
P = {"k": "Present"}
D = {"k": "Dropped"}
def A(d): return {"k": "Attenuated", "delta": d}
def Pred(p): return {"k": "Predicated", "predicate": p}
Intact = {"k": "Intact"}; Withheld = {"k": "Withheld"}; Severed = {"k": "Severed"}
Single = {"k": "Single"}
def Fused(t): return {"k": "Fused", "tau": t}
def fate(q, b, c, r): return {"quality": q, "bearer": b, "context": c, "record": r}
def grade(f, bo, m): return {"fate": f, "bond": bo, "merge": m}

def doc(nodes, edges, output, floor):
    return {"$schema": "https://github.com/hyperpolymath/trope-checker/schemas/trope-ir.schema.json",
            "$comment": SPDX, "version": "0.1", "profile": "prevent",
            "nodes": nodes, "edges": edges,
            "use_model": {"output": output, "floor": floor}}

def trope(id, present=("quality", "bearer", "context", "record")):
    return {"id": id, "type": "Trope", "present": list(present)}
def codomain(id, cod="Bool"): return {"id": id, "type": "Codomain", "codomain": cod}
def floating(id): return {"id": id, "type": "FloatingQuality", "present": ["quality"]}
def edge(id, effect, inputs, output, g, note=None):
    e = {"id": id, "effect": effect, "inputs": inputs, "output": output, "grade": g}
    if note: e["note"] = note
    return e
def write(d, name): (FIX / name).write_text(json.dumps(d, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

# ---- effect grades (the residual grade each effect contributes, composed via ▷) ----
def g_preserve(): return grade(fate(P, P, P, P), Intact, Single)
def g_collapse(pred): return grade(fate(Pred(pred), D, D, D), Withheld, Single)
def g_detach(): return grade(fate(P, D, D, D), Severed, Single)
def g_attenuate(d): return grade(fate(A(d), A(d), A(d), A(d)), Intact, Single)
def g_project(drop_bearer, dropped):
    f = fate(D if "quality" in dropped else P, D if "bearer" in dropped else P,
             D if "context" in dropped else P, D if "record" in dropped else P)
    return grade(f, Withheld if drop_bearer else Intact, Single)
def g_fuse(tau): return grade(fate(P, P, P, P), Intact, Fused(tau))

cases = []

write(doc([trope("duck"), trope("rec")],
          [edge("e_preserve", "preserve", ["duck"], "rec", g_preserve(),
                "lossless audio + ring number, pond, date, weather")],
          "rec", {"fate": {"quality": A(3)}}), "duck-preserve.ir.json")
cases.append({"ir": "duck-preserve.ir.json", "expect": "p-sufficient",
              "note": "preserve grade ε dominates every floor (calculus §Worked check)"})

write(doc([trope("duck"), codomain("yesno")],
          [edge("e_collapse", "collapse", ["duck"], "yesno", g_collapse("isQuack"),
                "the whole call became one yes/no")],
          "yesno", {"fate": {"quality": A(3)}}), "duck-collapse.ir.json")
cases.append({"ir": "duck-collapse.ir.json", "expect": "p-insufficient",
              "witness": "e_collapse", "witness_coordinate": "fate.quality",
              "note": "Predicated is below/incomparable to any Attenuated(δ) (calculus §Worked check)"})

write(doc([trope("attendee"), trope("badge", present=("quality", "context"))],
          [edge("e_project", "project", ["attendee"], "badge",
                g_project(True, {"bearer", "record"}),
                "badge prints name, pronouns, org; rest dropped by design")],
          "badge", {"fate": {"quality": P, "context": P}}), "badge-project.ir.json")
cases.append({"ir": "badge-project.ir.json", "expect": "p-sufficient",
              "note": "named intentional drop; the floor demands only what survives"})

write(doc([trope("attendee"), trope("badge", present=("quality", "context"))],
          [edge("e_project", "project", ["attendee"], "badge", g_project(True, {"bearer", "record"}))],
          "badge", {"bond": Intact}), "project-needs-bearer.ir.json")
cases.append({"ir": "project-needs-bearer.ir.json", "expect": "p-insufficient",
              "witness": "e_project", "witness_coordinate": "bond",
              "note": "projecting away the bearer → bond Withheld ⊏ Intact"})

write(doc([trope("letter"), trope("scan")],
          [edge("e_attenuate", "attenuate", ["letter"], "scan", g_attenuate("top"),
                "heavily compressed; couldn't say which strokes were lost")],
          "scan", {"fate": {"quality": A(5)}}), "letter-attenuate.ir.json")
cases.append({"ir": "letter-attenuate.ir.json", "expect": "p-insufficient",
              "witness": "e_attenuate", "witness_coordinate": "fate.quality",
              "note": "Attenuated(⊤) is below every finite attenuation (honest unknown)"})

write(doc([trope("interview"), floating("quote")],
          [edge("e_detach", "detach", ["interview"], "quote", g_detach(),
                "vivid line shared with no speaker, no question, no context")],
          "quote", {"bond": Intact}), "interview-detach.ir.json")
cases.append({"ir": "interview-detach.ir.json", "expect": "p-insufficient",
              "witness": "e_detach", "witness_coordinate": "bond",
              "note": "Severed ⊏ Intact; the type also becomes FloatingQuality"})

write(doc([trope("s1"), trope("s2"), trope("avg")],
          [edge("e_fuse", "fuse", ["s1", "s2"], "avg", g_fuse("average-of-12-stations"),
                "many readings blended into one, openly labelled")],
          "avg", {"merge": Fused("any")}), "weather-fuse.ir.json")
cases.append({"ir": "weather-fuse.ir.json", "expect": "p-sufficient",
              "note": "Fused ⊒ Fused; the label keeps plurality recoverable"})

write(doc([trope("s1"), trope("s2"), trope("avg")],
          [edge("e_fuse", "fuse", ["s1", "s2"], "avg", g_fuse("average-of-12-stations"))],
          "avg", {"merge": Single}), "fuse-needs-single.ir.json")
cases.append({"ir": "fuse-needs-single.ir.json", "expect": "p-insufficient",
              "witness": "e_fuse", "witness_coordinate": "merge",
              "note": "demanding Single but getting Fused → insufficient"})

write(doc([trope("t0"), trope("t1"), trope("t2")],
          [edge("e_att1", "attenuate", ["t0"], "t1", g_attenuate(3)),
           edge("e_att2", "attenuate", ["t1"], "t2", g_attenuate(4))],
          "t2", {"fate": {"quality": A(7)}}), "compose-attenuate-twice.ir.json")
cases.append({"ir": "compose-attenuate-twice.ir.json", "expect": "p-sufficient",
              "note": "Attenuated(3) ▷ Attenuated(4) = Attenuated(7) (tropical: losses add) (L1)"})

write(doc([trope("t0"), trope("t1"), codomain("bit")],
          [edge("e_att", "attenuate", ["t0"], "t1", g_attenuate(2)),
           edge("e_collapse", "collapse", ["t1"], "bit", g_collapse("isLoud"))],
          "bit", {"fate": {"quality": A(10)}}), "compose-attenuate-then-collapse.ir.json")
cases.append({"ir": "compose-attenuate-then-collapse.ir.json", "expect": "p-insufficient",
              "witness": "e_collapse", "witness_coordinate": "fate.quality",
              "note": "Attenuated(2) still meets floor A(10); the collapse edge drops below it"})

(REPO / "tests" / "conformance" / "cases.json").write_text(
    json.dumps({"$comment": SPDX, "cases": cases}, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

# ---- negative (schema-invalid) fixtures, each violating exactly one rule ----
def winv(d, name): (INV / name).write_text(json.dumps(d, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
winv(doc([trope("n0"), trope("n1")], [edge("e", "preserve", ["n0"], "n1", grade(fate(P, P, P, P), Severed, Single))], "n1", {"merge": Single}), "bearer-present-severed.json")
winv(doc([trope("n0"), trope("n1")], [edge("e", "project", ["n0"], "n1", grade(fate(P, D, P, P), Intact, Single))], "n1", {"merge": Single}), "bearer-absent-intact.json")
winv(doc([trope("n0"), trope("n1")], [edge("e", "fuse", ["n0", "n1"], "n1", grade(fate(P, P, P, P), Intact, {"k": "Conflated"}))], "n1", {"merge": Single}), "merge-conflated.json")
winv(doc([trope("n0"), trope("n1")], [edge("e", "preserve", ["n0"], "n1", grade(fate({"k": "Falsified"}, P, P, P), Intact, Single))], "n1", {"merge": Single}), "fate-falsified.json")
winv(doc([trope("n0"), trope("n1")], [edge("e", "preserve", ["n0"], "n1", grade(fate(P, P, P, P), {"k": "Misbound"}, Single))], "n1", {"merge": Single}), "bond-misbound.json")
winv(doc([trope("n0"), trope("n1")], [edge("e", "collapse", ["n0"], "n1", grade(fate(P, Pred("p"), P, P), Intact, Single))], "n1", {"merge": Single}), "predicated-on-bearer.json")
winv(doc([trope("n0"), trope("n1")], [edge("e", "fuse", ["n0", "n1"], "n1", grade(fate(P, P, P, P), Intact, {"k": "Fused"}))], "n1", {"merge": Single}), "untagged-fuse.json")
winv(doc([{"id": "n0", "type": "FloatingQuality", "present": ["quality", "bearer"]}], [], "n0", {"merge": Single}), "floatingquality-has-bearer.json")

# ---- verify positive cases against the checker ----
fail = 0
for c in cases:
    d = json.loads((FIX / c["ir"]).read_text())
    r = tc.check(d)
    ok = r["verdict"] == c["expect"]
    if ok and c.get("witness"):
        ok = r.get("witness") == c["witness"] and r.get("witness_coordinate") == c["witness_coordinate"]
    if not ok:
        fail += 1
        print(f"FAIL {c['ir']}: got {r}, expected {c['expect']}/{c.get('witness')}")
print(f"build_fixtures: {len(cases)} positive cases, {'all verified' if not fail else str(fail)+' FAILED'}")
sys.exit(1 if fail else 0)
