;; SPDX-License-Identifier: MPL-2.0
;; SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
;;
;; guix.scm — GNU Guix package definition for trope-checker.
;;
;; The language-independent consumer of Trope IR: it reads a JSON Trope IR
;; document and returns a verdict against each consumer's declared use-model.
;; Two implementations ship here — the Idris2 reference checker (built from the
;; verified core in verification/proofs/idris2, so the thing that runs is the
;; thing that is proved) and a dependency-free Rust fast core used to
;; cross-validate the same conformance corpus.
;;
;; Usage:
;;   guix shell -D -f build/guix.scm    # development shell
;;   guix build -f build/guix.scm       # build the package
;;
;; NOTE: the reference checker needs Idris 2 0.8.0 (see .tool-versions); Idris2
;; is not currently packaged for Guix here, so `build` covers the Rust fast core
;; and the conformance corpus. The Idris2 route is the digest-pinned container
;; used by .github/workflows/trope-check.yml.

(use-modules (guix packages)
             (guix gexp)
             (guix build-system gnu)
             ((guix licenses) #:prefix license:))

(package
  (name "trope-checker")
  (version "0.1.0")
  (source (local-file "." "trope-checker-checkout"
                      #:recursive? #t
                      #:select? (lambda (file stat)
                                  (not (string-contains file ".git")))))
  (build-system gnu-build-system)
  (synopsis "Trope IR conformance checker (IR -> graded verdict)")
  (description
   "trope-checker consumes a Trope IR document — a labelled DAG of
property-instance nodes joined by graded effect edges — and returns a verdict
of p-sufficient or p-insufficient against each consumer's declared use-model,
naming the offending edge and coordinate when it fails.  It never executes a
Haec program: the guarantee is about the IR, not about any one producer of it.")
  (home-page "https://github.com/hyperpolymath/trope-checker")
  ;; Code is MPL-2.0; the prose specification and docs are CC-BY-SA-4.0.
  (license (list license:mpl2.0 license:cc-by-sa4.0)))
