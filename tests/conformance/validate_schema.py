#!/usr/bin/env python3
# SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
# SPDX-License-Identifier: MPL-2.0
"""Validate the Trope IR schema and its fixtures (offline, no network).

  1. schemas/trope-ir.schema.json is a valid draft-2020-12 JSON Schema.
  2. every tests/conformance/fixtures/*.ir.json validates against it.
  3. every tests/conformance/schema-invalid/*.json is REJECTED, and the rejection
     names the offending coordinate (HC-3, HC-4: incoherent / deceptive states are
     unrepresentable, and the validator names where).
"""
from __future__ import annotations
import json, pathlib, sys

try:
    from jsonschema import Draft202012Validator
except ImportError:
    sys.exit("error: python 'jsonschema' package is required")

REPO = pathlib.Path(__file__).resolve().parents[2]
SCHEMA = REPO / "schemas" / "trope-ir.schema.json"
VALID = REPO / "tests" / "conformance" / "fixtures"
INVALID = REPO / "tests" / "conformance" / "schema-invalid"
GREEN, RED, DIM, OFF = "\033[32m", "\033[31m", "\033[2m", "\033[0m"


def load(p): return json.loads(p.read_text(encoding="utf-8"))


def main() -> int:
    failures = 0
    schema = load(SCHEMA)
    Draft202012Validator.check_schema(schema)
    v = Draft202012Validator(schema)
    print(f"{GREEN}ok{OFF}   schema is a valid draft-2020-12 JSON Schema")

    for path in sorted(VALID.glob("*.ir.json")):
        errs = sorted(v.iter_errors(load(path)), key=lambda e: list(e.absolute_path))
        if errs:
            failures += 1
            print(f"{RED}FAIL{OFF} {path.name} should validate but did not:")
            for e in errs:
                loc = "/".join(str(p) for p in e.absolute_path) or "<root>"
                print(f"     {DIM}{loc}{OFF}: {e.message}")
        else:
            print(f"{GREEN}ok{OFF}   {path.name} validates")

    if INVALID.is_dir():
        for path in sorted(INVALID.glob("*.json")):
            errs = sorted(v.iter_errors(load(path)), key=lambda e: list(e.absolute_path))
            if not errs:
                failures += 1
                print(f"{RED}FAIL{OFF} {path.name} should be REJECTED but validated")
            else:
                coord = "/".join(str(p) for p in errs[0].absolute_path) or "<root>"
                print(f"{GREEN}ok{OFF}   {path.name} rejected at {DIM}{coord}{OFF}")

    print(f"\n{(GREEN+'schema-check: all good') if not failures else (RED+f'schema-check: {failures} failure(s)')}{OFF}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
