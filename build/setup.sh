#!/bin/sh
# SPDX-License-Identifier: MPL-2.0
# setup.sh — Universal setup script for rsr-template-repo
#
# Detects your shell, platform, and installs prerequisites.
# Then hands off to `just setup` for project-specific configuration.
#
# Usage (after cloning — deliberately no curl|sh one-liner):
#   ./build/setup.sh
#
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)

set -eu

# ── Colours (safe — uses symbols too) ──
if [ -t 1 ] && command -v tput >/dev/null 2>&1; then
    RED=$(tput setaf 1 2>/dev/null || true)
    GREEN=$(tput setaf 2 2>/dev/null || true)
    YELLOW=$(tput setaf 3 2>/dev/null || true)
    CYAN=$(tput setaf 6 2>/dev/null || true)
    BOLD=$(tput bold 2>/dev/null || true)
    RESET=$(tput sgr0 2>/dev/null || true)
else
    RED="" GREEN="" YELLOW="" CYAN="" BOLD="" RESET=""
fi

ok()   { printf "  %s[OK]%s   %s\n" "$GREEN" "$RESET" "$1"; }
fail() { printf "  %s[FAIL]%s %s\n" "$RED" "$RESET" "$1"; }
warn() { printf "  %s[WARN]%s %s\n" "$YELLOW" "$RESET" "$1"; }
info() { printf "  %s[INFO]%s %s\n" "$CYAN" "$RESET" "$1"; }

# Run a command with elevation when the platform provides it. Root shells and
# containers should not fail merely because sudo is absent; OpenBSD's doas is
# the native equivalent.
as_root() {
    if [ "$(id -u 2>/dev/null || echo 1)" = "0" ]; then
        "$@"
    elif command -v sudo >/dev/null 2>&1; then
        sudo "$@"
    elif command -v doas >/dev/null 2>&1; then
        doas "$@"
    else
        fail "Root privileges required but neither sudo nor doas is available"
        return 127
    fi
}

# ── Shell Detection ──
detect_shell() {
    # Check the actual running shell, not just $SHELL
    CURRENT_SHELL="unknown"

    if [ -n "${BASH_VERSION:-}" ]; then CURRENT_SHELL="bash"
    elif [ -n "${ZSH_VERSION:-}" ]; then CURRENT_SHELL="zsh"
    elif [ -n "${FISH_VERSION:-}" ]; then CURRENT_SHELL="fish"
    elif [ -n "${KSH_VERSION:-}" ]; then CURRENT_SHELL="ksh"
    # Check by process name for shells that don't set version vars
    elif command -v ps >/dev/null 2>&1; then
        SHELL_PROC=$(ps -p $$ -o comm= 2>/dev/null || echo "unknown")
        case "$SHELL_PROC" in
            *dash*)    CURRENT_SHELL="dash" ;;
            *tcsh*)    CURRENT_SHELL="tcsh" ;;
            *csh*)     CURRENT_SHELL="csh" ;;
            *elvish*)  CURRENT_SHELL="elvish" ;;
            *nu*)      CURRENT_SHELL="nushell" ;;
            *oil*|*osh*) CURRENT_SHELL="oil" ;;
            *xonsh*)   CURRENT_SHELL="xonsh" ;;
            *murex*)   CURRENT_SHELL="murex" ;;
            *ion*)     CURRENT_SHELL="ion" ;;
            *hilbish*) CURRENT_SHELL="hilbish" ;;
            *oh*)      CURRENT_SHELL="oh" ;;
            *vsh*)     CURRENT_SHELL="vsh" ;;
            *pwsh*|*powershell*) CURRENT_SHELL="powershell" ;;
        esac
    fi

    # Fallback: check $SHELL env var
    if [ "$CURRENT_SHELL" = "unknown" ] && [ -n "${SHELL:-}" ]; then
        case "$SHELL" in
            */bash)  CURRENT_SHELL="bash" ;;
            */zsh)   CURRENT_SHELL="zsh" ;;
            */fish)  CURRENT_SHELL="fish" ;;
            */dash)  CURRENT_SHELL="dash" ;;
            */ksh*)  CURRENT_SHELL="ksh" ;;
            */tcsh)  CURRENT_SHELL="tcsh" ;;
            */csh)   CURRENT_SHELL="csh" ;;
            */vsh)   CURRENT_SHELL="vsh" ;;
        esac
    fi

    printf "%s" "$CURRENT_SHELL"
}

# ── Platform Detection ──
detect_platform() {
    OS="unknown"
    DISTRO="unknown"
    PKG_MGR="unknown"
    ARCH=$(uname -m 2>/dev/null || echo "unknown")

    case "$(uname -s 2>/dev/null)" in
        Linux*)
            OS="linux"
            if [ -f /etc/os-release ]; then
                # shellcheck source=/dev/null
                DISTRO=$(. /etc/os-release && echo "$ID")
            elif [ -f /etc/redhat-release ]; then
                DISTRO="rhel"
            elif [ -f /etc/debian_version ]; then
                DISTRO="debian"
            fi
            # Detect package manager
            if command -v dnf >/dev/null 2>&1; then PKG_MGR="dnf"
            elif command -v apt-get >/dev/null 2>&1; then PKG_MGR="apt"
            elif command -v pacman >/dev/null 2>&1; then PKG_MGR="pacman"
            elif command -v apk >/dev/null 2>&1; then PKG_MGR="apk"
            elif command -v zypper >/dev/null 2>&1; then PKG_MGR="zypper"
            elif command -v rpm-ostree >/dev/null 2>&1; then PKG_MGR="rpm-ostree"
            elif command -v guix >/dev/null 2>&1; then PKG_MGR="guix"
            fi
            ;;
        Darwin*)
            OS="macos"
            DISTRO="macos"
            if command -v brew >/dev/null 2>&1; then PKG_MGR="brew"
            elif command -v port >/dev/null 2>&1; then PKG_MGR="macports"
            fi
            ;;
        CYGWIN*|MINGW*|MSYS*)
            OS="windows"
            DISTRO="msys"
            if command -v winget >/dev/null 2>&1; then PKG_MGR="winget"
            elif command -v scoop >/dev/null 2>&1; then PKG_MGR="scoop"
            elif command -v choco >/dev/null 2>&1; then PKG_MGR="choco"
            fi
            ;;
        FreeBSD*)
            OS="freebsd"
            DISTRO="freebsd"
            PKG_MGR="pkg"
            ;;
        DragonFly*)
            OS="dragonfly"
            DISTRO="dragonfly"
            PKG_MGR="pkg"
            ;;
        OpenBSD*)
            OS="openbsd"
            DISTRO="openbsd"
            PKG_MGR="pkg_add"
            ;;
        NetBSD*)
            OS="netbsd"
            DISTRO="netbsd"
            if command -v pkgin >/dev/null 2>&1; then PKG_MGR="pkgin"
            else PKG_MGR="pkg_add"
            fi
            ;;
    esac
}

# ── Install just ──
# Install the pinned just release from a checksum-verified archive (never
# curl|bash - CWE-494). The matrix is exactly the vendor's 1.59.0 release
# matrix: Linux (x86_64, aarch64, arm, armv7, riscv64gc, loongarch64),
# macOS and Windows/MSYS (x86_64, aarch64). Other platforms use their package
# manager in install_just below or fail with manual instructions. Returns 1
# for an unsupported platform, a download/checksum failure, or an install
# failure; the temporary download is removed on every path.
install_just_pinned() {
    _just_version="1.59.0"
    _just_system=$(uname -s 2>/dev/null || echo unknown)
    _just_machine=$(uname -m 2>/dev/null || echo unknown)

    case "$_just_system" in
        Linux) _just_os="unknown-linux-musl"; _just_ext="tar.gz"; _just_binary="just" ;;
        Darwin) _just_os="apple-darwin"; _just_ext="tar.gz"; _just_binary="just" ;;
        CYGWIN*|MINGW*|MSYS*) _just_os="pc-windows-msvc"; _just_ext="zip"; _just_binary="just.exe" ;;
        *)
            fail "No pinned 'just' archive for $_just_system/$_just_machine - install manually: https://just.systems/"
            return 1
            ;;
    esac

    case "$_just_machine" in
        x86_64|amd64) _just_arch="x86_64" ;;
        aarch64|arm64) _just_arch="aarch64" ;;
        armv7*) _just_arch="armv7" ;;
        armv6*|armhf|arm) _just_arch="arm" ;;
        riscv64) _just_arch="riscv64gc" ;;
        loongarch64) _just_arch="loongarch64" ;;
        *)
            fail "No pinned 'just' archive for $_just_system/$_just_machine - install manually: https://just.systems/"
            return 1
            ;;
    esac

    if [ "$_just_os" != "unknown-linux-musl" ] \
        && [ "$_just_arch" != "x86_64" ] && [ "$_just_arch" != "aarch64" ]; then
        fail "No pinned 'just' archive for $_just_system/$_just_machine - install manually: https://just.systems/"
        return 1
    fi
    # The Linux ARM release triples spell the hard-float ABI out.
    if [ "$_just_os" = "unknown-linux-musl" ] \
        && { [ "$_just_arch" = "arm" ] || [ "$_just_arch" = "armv7" ]; }; then
        _just_os="unknown-linux-musleabihf"
    fi

    _just_asset="just-${_just_version}-${_just_arch}-${_just_os}.${_just_ext}"
    case "$_just_asset" in
        just-1.59.0-aarch64-apple-darwin.tar.gz) _just_sha="6574cea774ed4cae12e24b6aa11857de33e80dab4667cf628fd5840df96a2a9d" ;;
        just-1.59.0-aarch64-pc-windows-msvc.zip) _just_sha="a72808bc8f8028c25aaae87cf26405d2bd85d2769a779380b344c69607216971" ;;
        just-1.59.0-aarch64-unknown-linux-musl.tar.gz) _just_sha="23871b1702bfd550fb5f901778fd4290ecf2ee034a45a889fbe96d89b188086d" ;;
        just-1.59.0-arm-unknown-linux-musleabihf.tar.gz) _just_sha="080ea650f9aef32e0b371af71dc0c8dc3a355f74007ebbe350dc31d2fb510a02" ;;
        just-1.59.0-armv7-unknown-linux-musleabihf.tar.gz) _just_sha="928e2a0fe5fcade06415c55210608efefe43e985a757ded3e219ac4a13b6ed0e" ;;
        just-1.59.0-loongarch64-unknown-linux-musl.tar.gz) _just_sha="c6a684e2094e5a762e45765e35e7beac037f83fa44a521cd40221caa3a170179" ;;
        just-1.59.0-riscv64gc-unknown-linux-musl.tar.gz) _just_sha="698951bdc89869cd8a3c0229402944c628e67d1e41e9179d8ef2b35301b666b4" ;;
        just-1.59.0-x86_64-apple-darwin.tar.gz) _just_sha="036ead9df9bc31dbae9934ae3b4236ed124d0bafcffd33439460ae084d5c9cb7" ;;
        just-1.59.0-x86_64-pc-windows-msvc.zip) _just_sha="9c5463e2d0974e31bee71346aa5cbf19167de1585a4abc1bae7b3b04604ea9c0" ;;
        just-1.59.0-x86_64-unknown-linux-musl.tar.gz) _just_sha="409044617b6f06517c1035e55ca38c8c856ff8b650e41bc2aa1ef82d5903a23e" ;;
        *) fail "No checksum pinned for $_just_asset"; return 1 ;;
    esac
    _just_tmp=$(mktemp -d)
    if ! curl --fail --proto '=https' --proto-redir '=https' --tlsv1.2 -sSL \
        -o "$_just_tmp/$_just_asset" \
        "https://github.com/casey/just/releases/download/${_just_version}/${_just_asset}"; then
        fail "Could not download pinned just archive $_just_asset"
        rm -rf "$_just_tmp"
        return 1
    fi

    if command -v sha256sum >/dev/null 2>&1; then
        printf '%s  %s\n' "$_just_sha" "$_just_tmp/$_just_asset" | sha256sum -c - >/dev/null 2>&1
    elif command -v shasum >/dev/null 2>&1; then
        printf '%s  %s\n' "$_just_sha" "$_just_tmp/$_just_asset" | shasum -a 256 -c - >/dev/null 2>&1
    else
        fail "Neither sha256sum nor shasum is available to verify the just archive"
        rm -rf "$_just_tmp"
        return 1
    fi || {
        fail "just archive checksum mismatch"
        rm -rf "$_just_tmp"
        return 1
    }

    if [ "$_just_ext" = "zip" ]; then
        if ! command -v unzip >/dev/null 2>&1; then
            fail "unzip is required to extract the pinned Windows just archive"
            rm -rf "$_just_tmp"
            return 1
        fi
        unzip -q "$_just_tmp/$_just_asset" "$_just_binary" -d "$_just_tmp" || {
            fail "Could not extract $_just_binary from $_just_asset"
            rm -rf "$_just_tmp"
            return 1
        }
    else
        tar -xzf "$_just_tmp/$_just_asset" -C "$_just_tmp" "$_just_binary" || {
            fail "Could not extract $_just_binary from $_just_asset"
            rm -rf "$_just_tmp"
            return 1
        }
    fi

    _just_dest="/usr/local/bin"
    if [ -d "$_just_dest" ] && [ -w "$_just_dest" ] &&
        install -m 0755 "$_just_tmp/$_just_binary" "$_just_dest/$_just_binary"; then
        : # Installed without elevation.
    elif [ -d "$_just_dest" ] && { [ "$(id -u 2>/dev/null || echo 1)" = "0" ] ||
        command -v sudo >/dev/null 2>&1 || command -v doas >/dev/null 2>&1; } &&
        as_root install -m 0755 "$_just_tmp/$_just_binary" "$_just_dest/$_just_binary"; then
        : # Installed with elevation.
    elif [ -n "${HOME:-}" ]; then
        _just_dest="$HOME/.local/bin"
        if ! mkdir -p "$_just_dest" || ! install -m 0755 "$_just_tmp/$_just_binary" "$_just_dest/$_just_binary"; then
            fail "Could not install just into $_just_dest"
            rm -rf "$_just_tmp"
            return 1
        fi
        warn "Installing just into $_just_dest; ensure it is on PATH for future shells"
    else
        fail "No writable install directory for just"
        rm -rf "$_just_tmp"
        return 1
    fi
    rm -rf "$_just_tmp"
    PATH="$_just_dest${PATH:+:$PATH}"
    export PATH
}

# Ensure just is on PATH, reusing an existing installation when available.
# Every PKG_MGR value emitted by detect_platform has an arm here; an unknown
# manager uses the checksum-pinned vendor archive matrix above. May install
# system packages or write to an install directory with elevation. Returns 1
# if just remains unavailable.
install_just() {
    if command -v just >/dev/null 2>&1; then
        ok "just already installed: $(just --version 2>/dev/null | head -1)"
        return 0
    fi

    info "Installing just (task runner)..."

    case "$PKG_MGR" in
        dnf)        as_root dnf install -y just ;;
        apt)        as_root apt-get install -y just 2>/dev/null || {
                        # just is absent from older apt repositories.
                        install_just_pinned
                    } ;;
        pacman)     as_root pacman -S --noconfirm just ;;
        apk)        as_root apk add just ;;
        zypper)     as_root zypper --non-interactive install just ;;
        brew)       brew install just ;;
        macports)   as_root port install just ;;
        scoop)      scoop install just ;;
        winget)     winget install --exact --id Casey.Just ;;
        choco)      choco install just -y ;;
        # rpm-ostree layers packages for the next boot; Guix's profile may
        # not be on this process's PATH. The pinned binary is usable now.
        rpm-ostree|guix) install_just_pinned ;;
        pkg)        as_root pkg install -y just ;;
        pkg_add)    as_root pkg_add just ;;
        pkgin)      as_root pkgin -y install just ;;
        *)
            info "Using the pinned just release archive..."
            install_just_pinned
            ;;
    esac

    if command -v just >/dev/null 2>&1; then
        ok "just installed: $(just --version 2>/dev/null | head -1)"
    else
        fail "Could not install just. Install manually: https://just.systems/"
        return 1
    fi
}

# ── Main ──
main() {
    printf "%s=== rsr-template-repo Setup ===%s\n\n" "$BOLD" "$RESET"

    # Detect environment
    SHELL_NAME=$(detect_shell)
    detect_platform

    info "Shell:    $SHELL_NAME"
    info "Platform: $OS ($DISTRO)"
    info "Arch:     $ARCH"
    info "Packages: $PKG_MGR"
    printf "\n"

    # Warn about exotic shells
    case "$SHELL_NAME" in
        vsh)
            info "Valence Shell detected — experimental support"
            info "Falling back to POSIX sh for setup, vsh for post-setup"
            ;;
        nushell|elvish|murex|ion|hilbish|oil|xonsh|oh)
            info "$SHELL_NAME detected — using POSIX sh for setup"
            ;;
    esac

    # Step 1: Install just
    printf "%sStep 1: Install task runner%s\n" "$BOLD" "$RESET"
    install_just || { fail "Cannot proceed without just"; exit 1; }
    printf "\n"

    # Step 2: Check if we're in the repo directory
    if [ ! -f "Justfile" ] && [ ! -f "justfile" ]; then
        warn "Not in a repo directory (no Justfile found)"
        info "Clone first: git clone https://github.com/hyperpolymath/rsr-template-repo.git"
        info "Then: cd rsr-template-repo && ./setup.sh"
        exit 1
    fi

    # Step 3: Run just setup
    printf "%sStep 2: Project setup%s\n" "$BOLD" "$RESET"
    if just --list 2>/dev/null | grep -q "^setup "; then
        just setup
    elif just --list 2>/dev/null | grep -q "^setup-dev "; then
        just setup-dev
    else
        warn "No 'setup' recipe in Justfile — running 'just doctor' instead"
        just doctor 2>/dev/null || true
    fi
    printf "\n"

    # Step 4: Post-install security snapshot
    printf "%sStep 3: Security snapshot%s\n" "$BOLD" "$RESET"
    if command -v firewall-cmd >/dev/null 2>&1; then
        if firewall-cmd --state 2>/dev/null | grep -q running; then
            ok "Firewall: firewalld active"
        else
            warn "Firewall: firewalld installed but not running"
            info "  Enable: sudo systemctl enable --now firewalld"
        fi
    elif command -v ufw >/dev/null 2>&1; then
        if ufw status 2>/dev/null | grep -q "Status: active"; then
            ok "Firewall: ufw active"
        else
            warn "Firewall: ufw installed but not active"
            info "  Enable: sudo ufw enable"
        fi
    else
        warn "Firewall: none detected"
        case "$PKG_MGR" in
            dnf|rpm-ostree) info "  Install: sudo dnf install firewalld && sudo systemctl enable --now firewalld" ;;
            apt) info "  Install: sudo apt install ufw && sudo ufw enable" ;;
            *) info "  Install a firewall for your platform" ;;
        esac
    fi

    if command -v getenforce >/dev/null 2>&1; then
        SE_STATUS=$(getenforce 2>/dev/null || echo "unknown")
        case "$SE_STATUS" in
            Enforcing) ok "SELinux: Enforcing" ;;
            Permissive) warn "SELinux: Permissive (recommend Enforcing: sudo setenforce 1)" ;;
            *) warn "SELinux: $SE_STATUS" ;;
        esac
    fi

    # Write report
    REPORT_FILE="INSTALL-SECURITY-REPORT.adoc"
    {
        printf "// SPDX-License-Identifier: MPL-2.0\n"
        printf "= Install Security Report\n"
        printf ":date: %s\n\n" "$(date -Iseconds 2>/dev/null || date)"
        printf "== Platform\n"
        printf "* OS: %s (%s)\n" "$OS" "$DISTRO"
        printf "* Arch: %s\n" "$ARCH"
        printf "* Package manager: %s\n" "$PKG_MGR"
        printf "* Shell: %s\n\n" "$SHELL_NAME"
        printf "== Security Status\n"
        printf "Run \`just doctor\` for full diagnostic.\n"
    } > "$REPORT_FILE"
    info "Security report: $REPORT_FILE"
    printf "\n"

    # Done
    printf "%s=== Setup Complete ===%s\n\n" "${BOLD}${GREEN}" "$RESET"
    printf "Next steps:\n"
    printf "  just doctor     — verify everything works\n"
    printf "  just tour       — guided tour of the project\n"
    printf "  just build      — build the project\n"
    printf "  just help-me    — get help if stuck\n"
}

main "$@"
