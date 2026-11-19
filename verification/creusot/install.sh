#!/usr/bin/env bash
# SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
# SPDX-License-Identifier: MPL-2.0
#
# Install the pinned Creusot toolchain (verification/creusot/PINS). Used by
# .github/workflows/creusot.yml and by hand. Any failure exits non-zero: the
# gate is then RED, never silently green.
#
# Needs: git, rustup, opam (apt: opam), a C toolchain. Downloads: the creusot
# repo at the pinned SHA, the pinned nightly, why3/why3find from their pinned
# git commits (via opam), and alt-ergo/z3/cvc5 release binaries, which
# creusot's own installer checks against sha256 sums fixed in its source.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=/dev/null
source "$here/PINS"
dest="${CREUSOT_SRC:-$HOME/.cache/creusot-src}"

if [[ ! -d "$dest/.git" ]]; then
  git clone --quiet --depth 1 --branch "$CREUSOT_TAG" "$CREUSOT_REPO" "$dest"
fi
got="$(git -C "$dest" rev-parse HEAD)"
if [[ "$got" != "$CREUSOT_SHA" ]]; then
  echo "FAIL: $CREUSOT_TAG resolved to $got, pinned $CREUSOT_SHA" >&2
  exit 1
fi
want_nightly="$(sed -n 's/^channel = "\(.*\)"$/\1/p' "$dest/rust-toolchain")"
if [[ "$want_nightly" != "$RUST_NIGHTLY" ]]; then
  echo "FAIL: creusot wants $want_nightly, PINS says $RUST_NIGHTLY" >&2
  exit 1
fi
rustup toolchain install "$RUST_NIGHTLY" --profile minimal -c rustfmt,rustc-dev,llvm-tools

export OPAMYES=1
[[ -d "${OPAMROOT:-$HOME/.opam}" ]] || opam init --bare --disable-sandboxing -n
opam switch list 2>/dev/null | grep -q '^[ *→]*creusot ' \
  || opam switch create creusot "ocaml-base-compiler.$OCAML"
eval "$(opam env --switch=creusot)"
grep -q "$WHY3_GIT" "$dest/creusot-deps.opam" || { echo "FAIL: why3 pin drifted" >&2; exit 1; }
grep -q "$WHY3FIND_GIT" "$dest/creusot-deps.opam" || { echo "FAIL: why3find pin drifted" >&2; exit 1; }
(cd "$dest" && opam install --deps-only ./creusot-deps.opam)
(cd "$dest" && ./INSTALL)
cargo creusot --help >/dev/null
echo "creusot $CREUSOT_TAG installed"
