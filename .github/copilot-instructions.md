<!--
SPDX-License-Identifier: CC-BY-SA-4.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
<!-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk> -->
<!-- Authoritative source: docs/practice/AI-CONVENTIONS.adoc -->

# Copilot Instructions

## Before Writing Code

- Read `trope-checker_chora.deed` (the repo deed, at the root) first: it is the single machine-readable record.
- A2ML is retired: never create an `.a2ml` file.

## License

- SPDX: `MPL-2.0` on all new files.
- Never use AGPL-3.0.
- Copyright: `Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>`

## Code Style

- Use descriptive variable names.
- Annotate and document all files.
- Add SPDX header to every source file.
- Use `just` for build/test/lint commands.

## Banned Patterns

- Idris2: no `believe_me`, no `assert_total`
- Haskell: no `unsafeCoerce`, no `unsafePerformIO`
- OCaml: no `Obj.magic`
- Coq: no `Admitted`
- Lean: no `sorry`
- Rust: no `transmute` unless FFI with `// SAFETY:` comment

## Banned Languages

- No TypeScript, ReScript, Deno, Node.js/npm or Python here; this repo's languages are the `:languages` list in `trope-checker_chora.deed`.
- No Go (use Rust).

## Containers

- Use Podman, never Docker.
- Name the file `Containerfile`, never `Dockerfile`.
- Base image: `cgr.dev/chainguard/wolfi-base:latest`.

## ABI/FFI

- ABI definitions in Idris2 (`src/interface/Abi/`).
- FFI implementations in Zig (`src/interface/ffi/`).
- Generated C headers in `src/interface/generated/`.
