#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Exercise setup's real platform and just-install functions without network or root.
# The sourced functions invoke the mocks indirectly.
# shellcheck disable=SC2329
set -euo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
sed '$d' "$root/build/setup.sh" > "$work/setup-lib.sh"
(
  # shellcheck source=/dev/null
  . "$work/setup-lib.sh"
  uname() { case "$1" in -m) echo x86_64 ;; -s) echo DragonFly ;; esac; }
  detect_platform
  [ "$OS" = dragonfly ] && [ "$DISTRO" = dragonfly ] && [ "$PKG_MGR" = pkg ]
)
(
  # shellcheck source=/dev/null
  . "$work/setup-lib.sh"
  HOME="$work/home"; export HOME
  uname() { case "$1" in -m) echo x86_64 ;; -s) echo Linux ;; esac; }
  curl() { return 0; }
  sha256sum() { return 0; }
  tar() { printf '#!/bin/sh\necho just\n' > "$4/just"; }
  install() { case "$4" in /usr/local/bin/*) return 1 ;; *) /bin/cp "$3" "$4" && /bin/chmod +x "$4" ;; esac; }
  as_root() { return 1; }
  mkdir() { /bin/mkdir "$@"; }
  rm() { /bin/rm "$@"; }
  mktemp() { /usr/bin/mktemp "$@"; }
  unset PATH
  install_just_pinned
  [ "$PATH" = "$HOME/.local/bin" ] && [ -x "$HOME/.local/bin/just" ]
)
echo 'PASS: setup preserves DragonFly identity and falls back when elevation fails with PATH unset'
