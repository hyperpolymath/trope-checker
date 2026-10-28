#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Exercise the real affirmation check, axiom recipe, and uses-ref scanner.
# Run with: bash tests/workflows/review_regressions_test.sh
set -euo pipefail

ROOT=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
CHECK="$ROOT/.github/affirmation-trusted/check.sh"
for tool in git gpg gpgconf awk perl python3; do
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

echo "All $checks regression cases passed."
