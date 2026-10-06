#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
#
# install-tools.sh — Developer toolchain installer
#
# Detects and installs the required project toolchain (guix or mise).

set -euo pipefail

echo "=== RSR Toolchain Installer ==="

if [ -f "build/guix.scm" ] && command -v guix &>/dev/null; then
    echo "Guix detected. Verifying development shell..."
    guix shell -D -f build/guix.scm -- true && echo "Guix shell verified."
elif [ -f ".mise.toml" ] && command -v mise &>/dev/null; then
    echo "mise detected. Installing the pinned toolchain from .mise.toml..."
    mise install
else
    echo "No standard toolchain (Guix/mise) detected or installed."
    echo "Please refer to README.adoc for manual setup instructions."
fi

echo "Installer complete."
