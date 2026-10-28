#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Exercise the real affirmation check, axiom recipe, and uses-ref scanner.
# Run with: bash tests/workflows/review_regressions_test.sh
set -euo pipefail

ROOT=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
CHECK="$ROOT/.github/affirmation-trusted/check.sh"
for tool in git gpg gpgconf awk jq perl python3; do
  command -v "$tool" >/dev/null || { echo "Missing test prerequisite: $tool" >&2; exit 1; }
done

scratch=$(mktemp -d)
export GNUPGHOME="$scratch/gnupg"
# Keep signing fixtures independent of the developer's Git configuration.
export GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_GLOBAL=/dev/null
cleanup() {
  gpgconf --homedir "$GNUPGHOME" --kill gpg-agent
  if [[ -d "$scratch/revoked-gnupg" ]]; then
    gpgconf --homedir "$scratch/revoked-gnupg" --kill gpg-agent
  fi
  rm -rf -- "$scratch"
}
trap cleanup EXIT
mkdir -m 700 "$GNUPGHOME"
gpg --batch --pinentry-mode loopback --passphrase '' --quick-generate-key \
  'Fixture <fixture@example.invalid>' ed25519 sign 0 >"$scratch/keygen.log" 2>&1
fingerprint=$(gpg --batch --with-colons --list-secret-keys 2>/dev/null | awk -F: '$1 == "fpr" { print $10; exit }')
key="$scratch/public.asc"
gpg --armor --export "$fingerprint" >"$key"
case_log="$scratch/case.log"
checks=0
SIGNATURE_ERROR='::error::Affirmation commit signature'

fail() {
  echo "FAIL: $*" >&2
  cat "$case_log" >&2
  exit 1
}

expect_exit() {
  local expected=$1 actual
  shift
  if "$@" >"$case_log" 2>&1; then actual=0; else actual=$?; fi
  [[ "$actual" == "$expected" ]] || fail "expected exit $expected, got $actual: $*"
}

assert_contains() {
  local expected_text=$1
  grep -Fq -- "$expected_text" "$case_log" || fail "missing diagnostic: $expected_text"
}

pass() {
  checks=$((checks + 1))
  echo "PASS: $*"
}

fixture_git() { git -C "$repo" "$@"; }

new_repo() {
  repo=$(mktemp -d "$scratch/repo.XXXXXX")
  git -c init.templateDir= -C "$repo" init -q
  fixture_git config core.hooksPath /dev/null
  fixture_git config user.name Fixture
  fixture_git config user.email fixture@example.invalid
  fixture_git config gpg.format openpgp
  fixture_git config user.signingkey "$fingerprint"
  printf '%s\n' '= Fixture affirmation' 'A substantive snapshot.' 'Checks were performed.' \
    'The result was recorded.' 'The receipt is historical.' >"$repo/AFFIRMATION.adoc"
  fixture_git add AFFIRMATION.adoc
  fixture_git commit -q -S -m fixture
}

gate() {
  local expected_exit=$1 trusted_keys=${2:-}
  expect_exit "$expected_exit" env GITHUB_WORKSPACE="$repo" AFFIRMATION_REQUIRED=true \
    AFFIRMATION_TRUSTED_GPG_KEYS="$trusted_keys" AFFIRMATION_ALLOWED_SIGNERS= bash "$CHECK"
}

new_repo
gate 0
assert_contains '::notice::Affirmation commit signature cannot be checked: public key unavailable.'
pass 'unknown signing key is a notice'

gate 0 "$key"
assert_contains 'signature verified with a trusted key'
pass 'trusted signature passes'

new_repo
fixture_git cat-file commit HEAD >"$repo/original-commit"
perl -0pe 's/\n\nfixture/\n\ntampered fixture/' "$repo/original-commit" >"$repo/tampered-commit"
if cmp -s "$repo/original-commit" "$repo/tampered-commit"; then fail 'commit was not tampered'; fi
tampered=$(fixture_git hash-object -t commit -w "$repo/tampered-commit")
fixture_git reset -q --hard "$tampered"
gate 1 "$key"
assert_contains "$SIGNATURE_ERROR"
pass 'tampered signature fails'

new_repo
cat >"$repo/broken-gpg" <<'SH'
#!/bin/sh
echo '[GNUPG:] NEWSIG'
echo '[GNUPG:] ERRSIG 0123456789ABCDEF 22 10 00 1 1'
echo '[GNUPG:] ERROR verify 1'
exit 2
SH
chmod 700 "$repo/broken-gpg"
fixture_git config gpg.program "$repo/broken-gpg"
gate 1 "$key"
assert_contains "$SIGNATURE_ERROR"
pass 'other verification error fails'

new_repo
cat >"$repo/broken-gpg" <<'SH'
#!/bin/sh
echo '[GNUPG:] NEWSIG'
echo '[GNUPG:] ERRSIG 0123456789ABCDEF 22 10 00 1 9'
echo '[GNUPG:] NO_PUBKEY 0123456789ABCDEF'
echo '[GNUPG:] ERROR verify 1'
exit 2
SH
chmod 700 "$repo/broken-gpg"
fixture_git config gpg.program "$repo/broken-gpg"
gate 1
assert_contains "$SIGNATURE_ERROR"
pass 'missing key does not hide another verification error'

new_repo
printf 'stub\n' >"$repo/AFFIRMATION.adoc"
gate 1
assert_contains 'stub'
pass 'unknown key does not bypass document substance check'

new_repo
# Construct the negative fixture at runtime so the source debt scan does not
# mistake the deliberately invalid document for unfinished implementation.
printf '%s: update this receipt\n' 'TO''DO' >>"$repo/AFFIRMATION.adoc"
gate 1
assert_contains 'placeholders'
pass 'unknown key does not bypass document placeholder check'

new_repo
revoked_home="$scratch/revoked-gnupg"
mkdir -m 700 "$revoked_home"
gpg --homedir "$revoked_home" --batch --import "$key" >"$scratch/revoke.log" 2>&1
sed 's/:-----BEGIN/-----BEGIN/g' "$GNUPGHOME/openpgp-revocs.d/$fingerprint.rev" >"$scratch/revocation.asc"
gpg --homedir "$revoked_home" --batch --import "$scratch/revocation.asc" >>"$scratch/revoke.log" 2>&1
gpg --homedir "$revoked_home" --armor --export "$fingerprint" >"$scratch/revoked.asc"
gate 1 "$scratch/revoked.asc"
assert_contains "$SIGNATURE_ERROR"
pass 'revoked signature fails'

# Extract and execute the repository recipe, with only lake replaced by a stub.
audit="$scratch/axioms"
mkdir -p "$audit/bin"
for pkg in grade-boundary grade-factorisation; do
  mkdir -p "$audit/verification/proofs/lean4/$pkg"
  touch "$audit/verification/proofs/lean4/$pkg/Fixture.lean"
done
awk '
  /^build-lean:$/ { recipe = 1; next }
  recipe && NF && !/^    / { exit }
  recipe { sub(/^    /, ""); print }
' "$ROOT/build/just/proofs.just" >"$audit/audit.sh"
[[ -s "$audit/audit.sh" ]] || fail 'build-lean recipe was not extracted'
cat >"$audit/bin/lake" <<'SH'
#!/usr/bin/env bash
if [[ "$1" == build ]]; then exit 0; fi
for ((i=0; i<RECEIPT_COUNT; i++)); do
  printf '%s\n' "$RECEIPT"
done
SH
chmod 700 "$audit/bin/lake"
receipts=(
  "'Fixture' depends on axioms: [propext, Classical.choice, Quot.sound]"
  "/tmp/Fixture.lean:1:0: info: 'Fixture' depends on axioms: [Quot.sound]"
  "'Fixture' does not depend on any axioms"
  "'Fixture' depends on axioms: [propext, sorryAx]"
  "'Fixture' depends on axioms: [Unapproved.axiom]"
  "'Fixture' depends on axioms: propext"
  "'Fixture' depends on axioms: [propext] trailing text"
  "'Fixture' depends on axioms: [propext]"
)
for i in "${!receipts[@]}"; do
  count=30
  expected=1
  if ((i < 3)); then expected=0; fi
  if ((i == 7)); then count=0; fi
  (
    cd "$audit"
    expect_exit "$expected" env PATH="$audit/bin:$PATH" RECEIPT="${receipts[$i]}" \
      RECEIPT_COUNT="$count" bash audit.sh
  )
  if ((count == 0)); then
    assert_contains 'floor 50'
  elif ((expected != 0)); then
    assert_contains "${receipts[$i]}"
  fi
  pass "axiom receipt case $((i + 1))"
done

# The scanner itself is embedded Python in the existing workflow. Extract it
# verbatim to scratch; the test harness and checked-in implementation are Bash.
resolver="$scratch/resolver"
mkdir -p "$resolver/.github/workflows" "$resolver/bin"
awk '
  /- name: Every external uses ref resolves, and none floats/ { step = 1 }
  step && /python3 - <</ { code = 1; next }
  code && /^          PY$/ { exit }
  code { sub(/^          /, ""); print }
' "$ROOT/.github/workflows/workflow-linter.yml" >"$resolver/resolve.py"
[[ -s "$resolver/resolve.py" ]] || fail 'uses-ref scanner was not extracted'
printf 'uses: owner/repo@v1.2.3\n' >"$resolver/.github/workflows/one.yml"
printf 'uses: owner/other@main\n' >"$resolver/.github/workflows/two.yaml"
cat >"$resolver/bin/gh" <<'SH'
#!/bin/sh
printf '%s\n' "$*" >>"$CALL_LOG"
# Answer the resolver's three query shapes: canonical full_name for
# repos/<owner>/<repo> (CANONICAL_OVERRIDE simulates a moved repository),
# a non-empty path for reusable-workflow contents lookups, and bare
# success for commit/tag resolution.
case "$2" in
  */contents/*) printf '%s\n' 'contents-ok' ;;
  repos/*/*/*) : ;;
  repos/*/*) printf '%s\n' "${CANONICAL_OVERRIDE:-${2#repos/}}" ;;
esac
SH
chmod 700 "$resolver/bin/gh"
(
  cd "$resolver"
  expect_exit 1 env PATH="$resolver/bin:$PATH" CALL_LOG="$resolver/calls" python3 resolve.py
)
assert_contains 'two.yaml'
assert_contains 'floating ref'
pass 'uses-ref scanner checks .yaml and rejects floating refs'
printf 'uses: owner/other@v2.3.4\n' >"$resolver/.github/workflows/two.yaml"
(
  cd "$resolver"
  expect_exit 0 env PATH="$resolver/bin:$PATH" CALL_LOG="$resolver/calls" python3 resolve.py
)
assert_contains 'resolved 2 distinct external uses refs'
grep -Fq 'repos/owner/other/git/ref/tags/v2.3.4' "$resolver/calls" || fail 'second version tag was not resolved'
pass 'uses-ref scanner resolves exact tags in both extensions'

# Several reusable workflows from the SAME repo at the SAME ref (the standards
# lanes): the workflow-PATH existence check must run per coordinate, not once
# per (repo, ref) — otherwise a renamed sibling workflow passes this linter
# and dies invisibly at startup.
printf 'uses: owner/repo/.github/workflows/a.yml@v1.2.3\n' >"$resolver/.github/workflows/one.yml"
printf 'uses: owner/repo/.github/workflows/b.yml@v1.2.3\n' >"$resolver/.github/workflows/two.yaml"
: >"$resolver/calls"
(
  cd "$resolver"
  expect_exit 0 env PATH="$resolver/bin:$PATH" CALL_LOG="$resolver/calls" python3 resolve.py
)
grep -Fq 'repos/owner/repo/contents/.github/workflows/a.yml' "$resolver/calls" || fail 'first reusable path was not checked'
grep -Fq 'repos/owner/repo/contents/.github/workflows/b.yml' "$resolver/calls" || fail 'second reusable path was not checked (deduped by repo@ref)'
pass 'uses-ref scanner checks every reusable path at a shared repo@ref'

# A moved repository still resolves over REST/git (the redirect is followed),
# so pin resolution alone stays green while every reusable call under the old
# name dies at startup — the 2026-10-28 standards-transfer outage. Only the
# canonical full_name comparison sees it; simulate the move via the stub.
(
  cd "$resolver"
  expect_exit 1 env PATH="$resolver/bin:$PATH" CALL_LOG="$resolver/calls" \
    CANONICAL_OVERRIDE=newowner/other python3 resolve.py
)
assert_contains 'MOVED repository'
assert_contains 'newowner/other'
pass 'uses-ref scanner rejects a moved repository coordinate'

# Axiom-audit filter soundness (proofs.yml): extractor takes the jq program
# verbatim from between the axiom-filter-jq markers. A compiler-placeholder
# excuse keyed on name substrings alone could hide a source axiom given an
# internal-looking name (`private axiom forged_spec`); the filter must catch
# it declared AND undeclared, must not drop a real axiom behind an
# internal-looking declaration, and must still excuse genuine compiler IR.
axiomfilter="$scratch/axiom-filter"
mkdir -p "$axiomfilter"
python3 - "$ROOT/.github/workflows/proofs.yml" >"$axiomfilter/filter.jq" <<'PY'
import sys
lines = open(sys.argv[1]).read().splitlines()
begin = next(i for i, l in enumerate(lines) if 'axiom-filter-jq:begin' in l)
end = next(i for i, l in enumerate(lines) if 'axiom-filter-jq:end' in l)
block = lines[begin + 1:end]
assert 'jq -s' in block[0], block[0]
prog = []
for l in block[1:]:
    if "}'" in l and l.rstrip().endswith('\\'):
        prog.append('}')
        break
    prog.append(l)
sys.stdout.write('\n'.join(prog) + '\n')
PY

axiom_ok() { # declared-json expected-ok report-json
  printf '%s\n' "$3" >"$axiomfilter/report-x.json"
  jq -s --argjson declared_axioms "$1" -f "$axiomfilter/filter.jq" \
    "$axiomfilter/report-x.json" >"$case_log" || fail "axiom filter errored on: $3"
  [[ "$(jq -r .ok "$case_log")" == "$2" ]] || fail "axiom filter ok != $2 for: $3 (declared: $1)"
}

axiom_ok '[]' true  '{"audited":5,"axiomsUsed":["Classical.choice","npowBinRec._at.Inst._spec_2"],"violations":[]}'
axiom_ok '["forged_spec"]' false '{"audited":5,"axiomsUsed":["forged_spec"],"violations":[{"decl":"RealThm","axioms":["forged_spec"]}]}'
axiom_ok '[]' false '{"audited":5,"axiomsUsed":["forged_spec"],"violations":[{"decl":"RealThm","axioms":["forged_spec"]}]}'
axiom_ok '[]' false '{"audited":5,"axiomsUsed":["sorryAx"],"violations":[{"decl":"match_1","axioms":["sorryAx"]}]}'
axiom_ok '[]' true  '{"audited":5,"axiomsUsed":[],"violations":[{"decl":"foo._cstage1","axioms":["bar._at.X._spec_1"]}]}'
axiom_ok '["forged_spec"]' false '{"audited":5,"axiomsUsed":["_private.Grade.0.forged_spec"],"violations":[{"decl":"RealThm","axioms":["_private.Grade.0.forged_spec"]}]}'
axiom_ok '[]' false '{"audited":0,"axiomsUsed":[],"violations":[]}'
pass 'axiom-audit filter cannot hide a source axiom behind a compiler-internal name'

echo "All $checks regression cases passed."
