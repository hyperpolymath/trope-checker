#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# Inventory of the declarations the PWG ledger may cite as witnesses.
#
# Emits one line per exported declaration, `<prover>\t<fully-qualified name>`,
# read from the sources with comments stripped (tests/lib/strip-proof-comments.awk,
# which fails loudly on an unterminated comment or string). scripts/pwg-check.sh
# rule 6 resolves every `declarations` entry in verification/pwg.json against this
# list, so a witness that names nothing — a transliterated or renamed identifier —
# is a gate failure, not a silent row.
#
# This is a NAME inventory, not a kernel. It establishes that the cited name is
# declared where the ledger says; that the declaration proves the stated
# obligation is the receipt's business (PROOF-POLICY 8.2), not this script's.
#
#   agda : top-level (column-0) signatures in verification/proofs/agda/theorem-b/TB/,
#          qualified by the file's module (TB.<File>). `a b : T` declares both.
#          Declarations inside a `private` block are not exported and are not
#          listed. Constructors and record fields are not listed.
#   lean : theorem/lemma/def/abbrev/instance/structure/inductive/class/axiom/opaque
#          declarations under verification/proofs/lean4/ (no .lake), qualified by
#          the enclosing `namespace` stack. `section`/`end` are tracked so an
#          `end` closes the right scope.
#
# Usage: pwg-names.sh [REPO_ROOT]
set -euo pipefail
ROOT="${1:-$(cd "$(dirname "$0")/.." && pwd)}"
STRIP="$ROOT/tests/lib/strip-proof-comments.awk"
[ -f "$STRIP" ] || { echo "pwg-names: comment stripper missing at tests/lib/strip-proof-comments.awk" >&2; exit 2; }

AGDA_DIR="$ROOT/verification/proofs/agda/theorem-b/TB"
LEAN_DIR="$ROOT/verification/proofs/lean4"
[ -d "$AGDA_DIR" ] || { echo "pwg-names: no Agda sources at $AGDA_DIR" >&2; exit 2; }
[ -d "$LEAN_DIR" ] || { echo "pwg-names: no Lean sources at $LEAN_DIR" >&2; exit 2; }

n=0
while IFS= read -r -d '' f; do
  mod="TB.$(basename "$f" .agda)"
  awk -f "$STRIP" "$f" | awk -v mod="$mod" '
    BEGIN { print "agda\t" mod }
    # A column-0 line ends a private block or a data block; an indented line
    # continues it.
    /^[^ \t]/ { priv = 0; indata = 0 }
    /^private[ \t]*$/ { priv = 1; next }
    priv { next }
    # Constructors of a top-level `data … where` are exported as TB.<File>.<con>.
    /^data[ \t].*[ \t]where[ \t]*$/ { indata = 1; next }
    indata && /^[ \t]+[^ \t]/ {
      if (!match($0, / :( |$)/)) next
      head = substr($0, 1, RSTART - 1); sub(/^[ \t]+/, "", head)
      k = split(head, toks, /[ \t]+/)
      for (j = 1; j <= k; j++) if (toks[j] != "") print "agda\t" mod "." toks[j]
      next
    }
    /^[^ \t]/ {
      # `name : T` or a signature continued on the next line (`name :`).
      if (!match($0, / :( |$)/)) next
      colon = RSTART
      head = substr($0, 1, colon - 1)
      k = split(head, toks, /[ \t]+/)
      if (toks[1] ~ /^(data|record|module|open|import|infix|infixl|infixr|pattern|syntax|postulate|abstract|mutual|instance|variable|field|constructor)$/) next
      for (j = 1; j <= k; j++) if (toks[j] != "") print "agda\t" mod "." toks[j]
    }'
  n=$((n + 1))
done < <(find "$AGDA_DIR" -name '*.agda' -print0 | sort -z)
[ "$n" -gt 0 ] || { echo "pwg-names: found no .agda files -- an empty inventory would resolve nothing" >&2; exit 1; }

n=0
while IFS= read -r -d '' f; do
  awk -f "$STRIP" "$f" | awk '
    function joined(   s, i) { s = ""; for (i = 1; i <= depth; i++) if (ns[i] != "") s = s ns[i] "."; return s }
    {
      line = $0
      sub(/^[ \t]+/, "", line)
      if (match(line, /^namespace[ \t]+[^ \t]+/)) {
        name = line; sub(/^namespace[ \t]+/, "", name); sub(/[ \t].*$/, "", name)
        c = split(name, parts, ".")
        for (i = 1; i <= c; i++) { depth++; ns[depth] = parts[i]; kind[depth] = (i == 1 ? "ns" : "nsc") }
        next
      }
      if (line ~ /^(noncomputable[ \t]+)?section([ \t]|$)/) { depth++; ns[depth] = ""; kind[depth] = "sec"; next }
      if (line ~ /^end([ \t]|$)/) {
        # `end A.B` closes the components A and B; a bare `end` or `end S` closes one scope.
        name = line; sub(/^end[ \t]*/, "", name); sub(/[ \t].*$/, "", name)
        c = (name == "") ? 1 : split(name, parts, ".")
        if (depth > 0 && kind[depth] == "sec") c = 1
        for (i = 1; i <= c && depth > 0; i++) depth--
        next
      }
      # strip attributes and modifiers
      while (match(line, /^@\[[^]]*\][ \t]*/)) line = substr(line, RLENGTH + 1)
      while (match(line, /^(private|protected|noncomputable|unsafe|partial|nonrec|scoped|local)[ \t]+/)) {
        if (line ~ /^private[ \t]/) priv = 1
        line = substr(line, RLENGTH + 1)
      }
      if (match(line, /^(theorem|lemma|def|abbrev|instance|structure|inductive|class|axiom|opaque)[ \t]+[^ \t:({[]+/)) {
        name = substr(line, 1, RLENGTH); sub(/^[a-z]+[ \t]+/, "", name)
        if (!priv) print "lean\t" joined() name
      }
      priv = 0
    }'
  n=$((n + 1))
done < <(find "$LEAN_DIR" -name '*.lean' -not -path '*/.lake/*' -print0 | sort -z)
[ "$n" -gt 0 ] || { echo "pwg-names: found no .lean files -- an empty inventory would resolve nothing" >&2; exit 1; }
