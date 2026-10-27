#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# Run the checker end to end against the shared conformance corpus: IR verdicts,
# witness edges and coordinates, and rejection of schema-invalid input.
# Build the reference checker with `just trope-build` first, or select an
# alternative compiled checker with TROPECHECK_BIN (as `just trope-rust` does).
# The conformance runner checks jq and the binary and propagates failures.
#
# Usage: bash tests/e2e.sh or just e2e
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec bash "$SCRIPT_DIR/conformance/run.sh"
