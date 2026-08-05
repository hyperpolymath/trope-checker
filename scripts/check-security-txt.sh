#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# RFC 9116 security.txt validation — the body of the 🔴 Gate: .well-known check.
#
# Extracted from .github/workflows/wellknown-enforcement.yml so that the gate and
# its canonical-wrongness canaries run the SAME code (standards R10). A canary
# that re-implements a gate's logic proves only that it agrees with itself.
#
# Usage: check-security-txt.sh [ROOT]   (ROOT defaults to the current directory)
# Exit:  0 = valid, 1 = rejected.
set -uo pipefail
ROOT="${1:-.}"

err() { echo "::error::$*"; }

SECTXT=""
[ -f "$ROOT/.well-known/security.txt" ] && SECTXT="$ROOT/.well-known/security.txt"
[ -f "$ROOT/security.txt" ] && SECTXT="$ROOT/security.txt"

if [ -z "$SECTXT" ]; then
  err "No security.txt found — required for OpenSSF Best Practices. See https://github.com/hyperpolymath/well-known-ecosystem"
  exit 1
fi

grep -q "^Contact:" "$SECTXT" || { err "Missing Contact field"; exit 1; }
grep -q "^Expires:" "$SECTXT" || { err "Missing Expires field"; exit 1; }

EXPIRES=$(grep "^Expires:" "$SECTXT" | cut -d: -f2- | tr -d ' ' | head -1)

# An Expires value that cannot be parsed used to skip the expiry check entirely,
# so an unparseable date passed the gate silently. RFC 9116 requires a valid
# ISO 8601 timestamp; an unreadable one is a violation, not an exemption.
if ! date -d "$EXPIRES" >/dev/null 2>&1; then
  err "Expires value '$EXPIRES' is not a parseable date (RFC 9116 requires ISO 8601)"
  exit 1
fi

DAYS=$(( ($(date -d "$EXPIRES" +%s) - $(date +%s)) / 86400 ))
if [ "$DAYS" -lt 0 ]; then
  err "security.txt EXPIRED ($((-DAYS)) days ago)"
  exit 1
elif [ "$DAYS" -lt 30 ]; then
  echo "::warning::security.txt expires in $DAYS days"
else
  echo "✅ security.txt valid ($DAYS days)"
fi
