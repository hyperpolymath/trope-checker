#!/usr/bin/env python3
# SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
# SPDX-License-Identifier: MPL-2.0
"""Run the machine conformance suite: every IR fixture -> expected verdict.

The corpus (cases.json + fixtures/) is the formal sibling of the human
particularity trainer: any tropechecker implementation MUST reproduce these
verdicts (and witness edges) to claim conformance (calculus §9.3). This runner
drives the reference executable checker (src/checker/tropecheck.py).
"""
from __future__ import annotations
import json, pathlib, sys

REPO = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "src" / "checker"))
import tropecheck as tc  # noqa: E402

CASES = REPO / "tests" / "conformance" / "cases.json"
FIX = REPO / "tests" / "conformance" / "fixtures"
GREEN, RED, DIM, OFF = "\033[32m", "\033[31m", "\033[2m", "\033[0m"


def main() -> int:
    spec = json.loads(CASES.read_text(encoding="utf-8"))
    failures = 0
    for c in spec["cases"]:
        doc = json.loads((FIX / c["ir"]).read_text(encoding="utf-8"))
        r = tc.check(doc)
        ok = r["verdict"] == c["expect"]
        detail = ""
        if ok and "witness" in c:
            if r.get("witness") != c["witness"] or r.get("witness_coordinate") != c.get("witness_coordinate"):
                ok, detail = False, (f" witness {r.get('witness')}/{r.get('witness_coordinate')}"
                                     f" != {c['witness']}/{c.get('witness_coordinate')}")
        if ok:
            w = (f" {DIM}witness={r.get('witness')}/{r.get('witness_coordinate')}{OFF}"
                 if r["verdict"] != "p-sufficient" else "")
            print(f"{GREEN}ok{OFF}   {c['ir']} → {r['verdict']}{w}")
        else:
            failures += 1
            print(f"{RED}FAIL{OFF} {c['ir']}: got {r['verdict']}, expected {c['expect']}{detail}")

    n = len(spec["cases"])
    print(f"\n{(GREEN+f'conformance: {n}/{n} passed') if not failures else (RED+f'conformance: {failures}/{n} failed')}{OFF}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
