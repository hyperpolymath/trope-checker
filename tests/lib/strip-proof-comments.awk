# Strip comments from proof/source files before scanning for dangerous constructs.
#
# Line-based filtering is not enough: a Coq (* ... *) or Lean /- ... -/ block
# spans lines, and a CONTINUATION line carries no marker of its own. Measured
# 2026-07-29: line 6 of the (since removed) Coq proof template ("All proofs must be
# complete - NO Admitted allowed.") is line 6 of a block comment and was
# reported as a dangerous construct -- i.e. the repo was failed for DOCUMENTING
# that it forbids Admitted.
#
# A comment marker inside a STRING LITERAL is not a comment. Measured 2026-11-09:
# `def m : String := "/-"` opened a block comment that swallowed the rest of the
# file, so an `axiom` declared after it was invisible to every gate that scans
# through here -- while awk still exited 0. Strings are therefore consumed as
# units and emitted as `""`. Emitting them blank is strictly safer than verbatim:
# a string whose CONTENT is the word `axiom` or `sorry` can no longer trip the
# gate either.
#
# Char literals ('c', '\n', '"') are skipped whole, because they cannot contain a
# digraph -- but only where the quote is not a prime on an identifier. Both halves
# of that are load-bearing. Without the skip, the `'"'` in
# `src/idris2/Checker/Json.idr` opens a string and swallows the lines after it,
# which re-creates this very hole in another file. Without the prime guard, the
# primed identifiers Lean and Idris2 use everywhere (h', n') are read as quotes.
#
# Unterminated block comment or string => exit 1, loudly. A truncated scan must
# never be reported as a clean one; that is what made the hole above invisible.
#
# Handles: (* *)  /- -/  {- -}  /* */  plus the line forms -- and //
#
# KNOWN LIMITATION, deliberately not fixed here: Lean 4 block comments NEST, and
# this stripper closes on the first `-/`. That direction is fail-LOUD (an honest
# file can be failed for text inside a nested comment), not fail-open, so it is a
# separable change rather than a hole. Tracked separately.
BEGIN { inblk = 0; instr = 0 }
{
  line = $0; out = ""; i = 1; n = length(line)
  while (i <= n) {
    two = substr(line, i, 2)
    if (inblk) {
      if (two == close_tok) { inblk = 0; i += 2; continue }
      i++; continue
    }
    if (instr) {
      c = substr(line, i, 1)
      if (c == "\\") { i += 2; continue }
      if (c == "\"") { instr = 0; i++; continue }
      i++; continue
    }
    if (two == "(*") { inblk = 1; close_tok = "*)"; i += 2; continue }
    if (two == "/-") { inblk = 1; close_tok = "-/"; i += 2; continue }
    if (two == "{-") { inblk = 1; close_tok = "-}"; i += 2; continue }
    if (two == "/*") { inblk = 1; close_tok = "*/"; i += 2; continue }
    if (two == "--" || two == "//") { break }
    c = substr(line, i, 1)
    if (c == "'" && substr(line, i - 1, 1) !~ /[A-Za-z0-9_'?!]/) {
      rest = substr(line, i)
      if (match(rest, /^'\\.'/) || match(rest, /^'\\[^']*'/) || match(rest, /^'[^'\\]'/)) {
        i += RLENGTH; continue
      }
    }
    if (c == "\"") { instr = 1; out = out "\"\""; i++; continue }
    out = out c; i++
  }
  print out
}
END {
  if (inblk) {
    print "strip-proof-comments: unterminated block comment (" close_tok " missing) -- refusing to report a truncated scan as clean" > "/dev/stderr"
    exit 1
  }
  if (instr) {
    print "strip-proof-comments: unterminated string literal -- refusing to report a truncated scan as clean" > "/dev/stderr"
    exit 1
  }
}
