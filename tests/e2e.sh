#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# Run the IR-to-verdict conformance corpus, including witness checks and
# schema-invalid rejection, against the built checker.
# Build first with `just trope-build`, then run `bash tests/e2e.sh` or `just e2e`.
# TROPECHECK_BIN can select an alternative checker, as in `just trope-rust`.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec bash "$SCRIPT_DIR/conformance/run.sh"
