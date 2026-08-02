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
;; Guix is the estate PRIMARY and only packager (ruled 2026-05-18; the Nix
;; mirror was removed from this repo). The inputs below still need filling
;; in against the real toolchain — see the TODOs.
;; See: https://guix.gnu.org/manual/en/html_node/Defining-Packages.html

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
  (arguments
   '(#:phases
     (modify-phases %standard-phases
       ;; TODO: Customize build phases for your project
       ;; Examples for common stacks:
       ;;
       ;; Rust:
       ;;   (replace 'build (lambda _ (invoke "cargo" "build" "--release")))
       ;;   (replace 'check (lambda _ (invoke "cargo" "test")))
       ;;
       ;; Elixir:
       ;;   (replace 'build (lambda _ (invoke "mix" "compile")))
       ;;   (replace 'check (lambda _ (invoke "mix" "test")))
       ;;
       ;; Zig:
       ;;   (replace 'build (lambda _ (invoke "zig" "build")))
       ;;   (replace 'check (lambda _ (invoke "zig" "build" "test")))
       (delete 'configure)
       (delete 'build)
       (delete 'check)
       (replace 'install
         (lambda* (#:key outputs #:allow-other-keys)
           (let ((out (assoc-ref outputs "out")))
             (mkdir-p (string-append out "/share/doc"))
             (copy-file "README.adoc"
                        (string-append out "/share/doc/README.adoc"))))))))
  (native-inputs
   (list
    ;; TODO: Add build-time dependencies
    ;; Examples:
    ;;   rust (gnu packages rust)
    ;;   elixir (gnu packages elixir)
    ;;   zig (gnu packages zig)
    ))
  (inputs
   (list
    ;; TODO: Add runtime dependencies
    ))
  (home-page "https://github.com/hyperpolymath/trope-checker")
  (synopsis "The portable trust boundary of the trope-particularity calculus: a pure function from a language-neutral Trope IR to a sufficiency verdict.")
  (description "RSR-compliant project. See README.adoc for details.")
  (license (list
            ;; MPL-2.0 extends MPL-2.0
            mpl2.0)))
