<!--
SPDX-License-Identifier: CC-BY-SA-4.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# Contributing

The full guide is `CONTRIBUTING.adoc` at the repository root; this file is the GitHub-facing summary.

### Development Setup
```bash
# Clone the repository
git clone https://github.com/hyperpolymath/trope-checker.git
cd trope-checker

# Using toolbox/distrobox
toolbox create trope-checker-dev
toolbox enter trope-checker-dev
# Install dependencies manually

# Verify setup
just check
just test    # Run test suite
```

### Repository Structure
```
trope-checker/
├── src/                 # Checker sources: idris2/ (calculus), rust/, interface/ (Abi, ffi)
├── spec/                # Calculus and Trope IR specifications
├── schemas/             # trope-ir.schema.json
├── verification/        # Proofs, coverage, fuzzing, safety case
├── tests/               # Conformance, e2e, aspect and workflow tests
├── benches/             # Benchmarks
├── examples/            # Examples
├── tools/               # Tooling
├── docs/                # Documentation (architecture, decisions, governance)
├── .machine_readable/   # Support files; the repo deed is the record
├── .well-known/         # Protocol files (Perimeter 1-3)
├── .github/             # GitHub config (CONTRIBUTING.md, CODE_OF_CONDUCT.md, workflows)
├── CHANGELOG.adoc
├── CONTRIBUTING.adoc
├── GOVERNANCE.adoc
├── LICENSE
├── MAINTAINERS.adoc
├── README.adoc
├── SECURITY.adoc
├── trope-checker_chora.deed  # The repo deed
├── build/guix.scm       # Guix package
└── Justfile             # Task runner
```

---

## How to Contribute

### Reporting Bugs

**Before reporting**:
1. Search existing issues
2. Check if it's already fixed in `main`
3. Determine which perimeter the bug affects

**When reporting**:

Open an issue and include:

- Clear, descriptive title
- Environment details (OS, versions, toolchain)
- Steps to reproduce
- Expected vs actual behaviour
- Logs, screenshots, or minimal reproduction

### Suggesting Features

**Before suggesting**:
1. Check the [roadmap](../docs/status/ROADMAP.adoc)
2. Search existing issues and discussions
3. Consider which perimeter the feature belongs to

**When suggesting**:

Open an issue and include:

- Problem statement (what pain point does this solve?)
- Proposed solution
- Alternatives considered
- Which perimeter this affects

### Your First Contribution

Look for issues labelled:

- [`good first issue`](https://github.com/hyperpolymath/trope-checker/labels/good%20first%20issue) — Simple Perimeter 3 tasks
- [`help wanted`](https://github.com/hyperpolymath/trope-checker/labels/help%20wanted) — Community help needed
- [`documentation`](https://github.com/hyperpolymath/trope-checker/labels/documentation) — Docs improvements
- [`perimeter-3`](https://github.com/hyperpolymath/trope-checker/labels/perimeter-3) — Community sandbox scope

---

## Development Workflow

### Branch Naming
```
docs/short-description       # Documentation (P3)
test/what-added              # Test additions (P3)
feat/short-description       # New features (P2)
fix/issue-number-description # Bug fixes (P2)
refactor/what-changed        # Code improvements (P2)
security/what-fixed          # Security fixes (P1-2)
```

### Commit Messages

We follow [Conventional Commits](https://www.conventionalcommits.org/):
```
<type>(<scope>): <description>

[optional body]

[optional footer]

## Signed commits

Every commit that reaches the default branch must be signed; a ruleset refuses
unsigned pushes. Estate policy:
[SIGNING-POLICY](https://github.com/hyperpolymath/standards/blob/main/docs/SIGNING-POLICY.adoc).

- **People and interactive agents** sign with an SSH key registered on GitHub
  as a *signing* key (`gpg.format=ssh`, `user.signingkey=<key>.pub`,
  `commit.gpgsign=true`). The committer email must be verified on that account.
- **Apps, bots and workflows** never `git push` local commits. They write
  through the API (`createCommitOnBranch` or the estate `signed-push` action)
  so that GitHub signs each commit.
- Merge PRs with **squash**. The ruleset checks every commit on the PR branch,
  not just the result, so one unsigned commit blocks the merge. Re-create such a
  branch with signed commits (`git cherry-pick -S`) and open a new PR.
  Rebase-merge replays commits unsigned and is disabled.
