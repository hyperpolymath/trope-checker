#!/usr/bin/env python3
# SPDX-License-Identifier: MPL-2.0
"""Exercise the real affirmation check, axiom recipe, and uses-ref scanner."""

import os
from pathlib import Path
import subprocess
import tempfile
import textwrap
import unittest

ROOT = Path(__file__).resolve().parents[2]
CHECK = ROOT / '.github/affirmation-trusted/check.sh'


def run(args, cwd, env=None, check=True):
    return subprocess.run(args, cwd=cwd, env=env, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          check=check)


class AffirmationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.scratch = tempfile.TemporaryDirectory()
        cls.base = Path(cls.scratch.name)
        cls.home = cls.base / 'gnupg'
        cls.home.mkdir(mode=0o700)
        cls.env = dict(os.environ, GNUPGHOME=str(cls.home))
        run(['gpg', '--batch', '--pinentry-mode', 'loopback', '--passphrase', '',
             '--quick-generate-key', 'Fixture <fixture@example.invalid>',
             'ed25519', 'sign', '0'], cls.base, cls.env)
        result = run(['gpg', '--batch', '--with-colons', '--list-secret-keys'],
                     cls.base, cls.env)
        cls.fingerprint = next(line.split(':')[9] for line in result.stdout.splitlines()
                               if line.startswith('fpr:'))
        cls.key = cls.base / 'public.asc'
        cls.key.write_text(run(['gpg', '--armor', '--export', cls.fingerprint],
                               cls.base, cls.env).stdout)

    @classmethod
    def tearDownClass(cls):
        run(['gpgconf', '--kill', 'gpg-agent'], cls.base, cls.env)
        cls.scratch.cleanup()

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(dir=self.base)
        self.addCleanup(self.tmp.cleanup)
        self.repo = Path(self.tmp.name)
        run(['git', 'init', '-q'], self.repo)
        for key, value in [('user.name', 'Fixture'), ('user.email', 'fixture@example.invalid'),
                           ('gpg.format', 'openpgp'), ('user.signingkey', self.fingerprint)]:
            run(['git', 'config', key, value], self.repo)
        (self.repo / 'AFFIRMATION.adoc').write_text(
            '= Fixture affirmation\nA substantive snapshot.\nChecks were performed.\n'
            'The result was recorded.\nThe receipt is historical.\n')
        run(['git', 'add', 'AFFIRMATION.adoc'], self.repo)
        run(['git', 'commit', '-q', '-S', '-m', 'fixture'], self.repo, self.env)

    def gate(self, trusted=False):
        env = dict(self.env, GITHUB_WORKSPACE=str(self.repo), AFFIRMATION_REQUIRED='true',
                   AFFIRMATION_TRUSTED_GPG_KEYS=str(self.key) if trusted else '',
                   AFFIRMATION_ALLOWED_SIGNERS='')
        return run(['bash', str(CHECK)], self.repo, env, check=False)

    def test_unknown_key_is_notice(self):
        result = self.gate()
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn('::notice::Affirmation commit signature cannot be checked: public key unavailable.',
                      result.stdout)

    def test_trusted_signature_passes(self):
        result = self.gate(trusted=True)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn('signature verified with a trusted key', result.stdout)

    def test_bad_signature_fails(self):
        commit = run(['git', 'cat-file', 'commit', 'HEAD'], self.repo).stdout
        tampered = commit.replace('\n\nfixture', '\n\ntampered fixture')
        self.assertNotEqual(commit, tampered)
        hashed = subprocess.run(['git', 'hash-object', '-t', 'commit', '-w', '--stdin'],
                                cwd=self.repo, input=tampered, text=True,
                                stdout=subprocess.PIPE, check=True).stdout.strip()
        run(['git', 'reset', '--hard', hashed], self.repo)
        result = self.gate(trusted=True)
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn('::error::Affirmation commit signature', result.stdout)

    def test_other_verification_error_fails(self):
        verifier = self.repo / 'broken-gpg'
        verifier.write_text('#!/bin/sh\necho "[GNUPG:] NEWSIG"\n'
                            'echo "[GNUPG:] ERRSIG 0123456789ABCDEF 22 10 00 1 1"\n'
                            'echo "[GNUPG:] ERROR verify 1"\nexit 2\n')
        verifier.chmod(0o700)
        run(['git', 'config', 'gpg.program', str(verifier)], self.repo)
        result = self.gate(trusted=True)
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn('::error::Affirmation commit signature', result.stdout)

    def test_missing_key_with_another_error_still_fails(self):
        verifier = self.repo / 'broken-gpg'
        verifier.write_text('#!/bin/sh\necho "[GNUPG:] NEWSIG"\n'
                            'echo "[GNUPG:] ERRSIG 0123456789ABCDEF 22 10 00 1 9"\n'
                            'echo "[GNUPG:] NO_PUBKEY 0123456789ABCDEF"\n'
                            'echo "[GNUPG:] ERROR verify 1"\nexit 2\n')
        verifier.chmod(0o700)
        run(['git', 'config', 'gpg.program', str(verifier)], self.repo)
        result = self.gate()
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn('::error::Affirmation commit signature', result.stdout)

    def test_unknown_key_does_not_bypass_document_validation(self):
        path = self.repo / 'AFFIRMATION.adoc'
        for body, expected in [('stub\n', 'stub'),
                               (path.read_text() + 'TODO: update this receipt\n', 'placeholders')]:
            with self.subTest(expected=expected):
                path.write_text(body)
                result = self.gate()
                self.assertEqual(result.returncode, 1, result.stdout)
                self.assertIn(expected, result.stdout)

    def test_revoked_signature_fails(self):
        # Work on a separate keyring so other cases keep their valid signing key.
        home = self.repo / 'revoked-gnupg'
        home.mkdir(mode=0o700)
        env = dict(self.env, GNUPGHOME=str(home))
        run(['gpg', '--batch', '--import', str(self.key)], self.repo, env)
        revocation = (self.home / 'openpgp-revocs.d' / (self.fingerprint + '.rev')).read_text()
        cert = self.repo / 'revocation.asc'
        cert.write_text(revocation.replace(':-----BEGIN', '-----BEGIN'))
        run(['gpg', '--batch', '--import', str(cert)], self.repo, env)
        self.addCleanup(run, ['gpgconf', '--kill', 'gpg-agent'], self.repo, env)
        revoked_key = self.repo / 'revoked.asc'
        revoked_key.write_text(run(['gpg', '--armor', '--export', self.fingerprint],
                                   self.repo, env).stdout)
        result = run(['bash', str(CHECK)], self.repo,
                     dict(self.env, GITHUB_WORKSPACE=str(self.repo),
                          AFFIRMATION_TRUSTED_GPG_KEYS=str(revoked_key),
                          AFFIRMATION_ALLOWED_SIGNERS=''), check=False)
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn('::error::Affirmation commit signature', result.stdout)


class AxiomAuditTests(unittest.TestCase):
    def test_receipts_and_failure_diagnostics(self):
        source = (ROOT / 'build/just/proofs.just').read_text().split('build-lean:\n', 1)[1]
        lines = []
        for line in source.splitlines():
            if line and not line.startswith('    '):
                break
            lines.append(line[4:] if line.startswith('    ') else line)
        recipe = '\n'.join(lines) + '\n'
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            for pkg in ['grade-boundary', 'grade-factorisation']:
                path = base / 'verification/proofs/lean4' / pkg
                path.mkdir(parents=True)
                (path / 'Fixture.lean').touch()
            lake = base / 'lake'
            lake.write_text('#!/bin/bash\nif [ "$1" = build ]; then exit 0; fi\n'
                            'for ((i=0; i<RECEIPT_COUNT; i++)); do\n'
                            '  printf "%s\\n" "$RECEIPT"\ndone\n')
            lake.chmod(0o700)
            script = base / 'audit.sh'
            script.write_text(recipe)
            cases = [
                ("'Fixture' depends on axioms: [propext, Classical.choice, Quot.sound]", 30, 0),
                ("/tmp/Fixture.lean:1:0: info: 'Fixture' depends on axioms: [Quot.sound]", 30, 0),
                ("'Fixture' does not depend on any axioms", 30, 0),
                ("'Fixture' depends on axioms: [propext, sorryAx]", 30, 1),
                ("'Fixture' depends on axioms: [Unapproved.axiom]", 30, 1),
                ("'Fixture' depends on axioms: propext", 30, 1),
                ("'Fixture' depends on axioms: [propext] trailing text", 30, 1),
                ("'Fixture' depends on axioms: [propext]", 0, 1),
            ]
            for receipt, count, expected in cases:
                with self.subTest(receipt=receipt, count=count):
                    result = run(['bash', str(script)], base,
                                 dict(os.environ, PATH=str(base) + os.pathsep + os.environ['PATH'],
                                      RECEIPT=receipt, RECEIPT_COUNT=str(count)), check=False)
                    self.assertEqual(result.returncode, expected, result.stdout)
                    if expected and count:
                        self.assertIn(receipt, result.stdout)
                    if not count:
                        self.assertIn('floor 50', result.stdout)


class WorkflowResolverTests(unittest.TestCase):
    def test_both_extensions_are_resolved_and_floating_refs_fail(self):
        workflow = (ROOT / '.github/workflows/workflow-linter.yml').read_text()
        step = workflow.split('      - name: Every external uses ref resolves, and none floats', 1)[1]
        code = textwrap.dedent(step.split("python3 - <<'PY'\n", 1)[1].split('\n          PY', 1)[0])
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            workflows = base / '.github/workflows'
            workflows.mkdir(parents=True)
            (workflows / 'one.yml').write_text('uses: owner/repo@v1.2.3\n')
            other = workflows / 'two.yaml'
            other.write_text('uses: owner/other@main\n')
            gh = base / 'gh'
            gh.write_text('#!/bin/sh\nprintf "%s\\n" "$*" >> "$CALL_LOG"\n')
            gh.chmod(0o700)
            script = base / 'resolve.py'
            script.write_text(code)
            log = base / 'calls'
            env = dict(os.environ, PATH=str(base) + os.pathsep + os.environ['PATH'],
                       CALL_LOG=str(log))
            result = run(['python3', str(script)], base, env, check=False)
            self.assertEqual(result.returncode, 1, result.stdout)
            self.assertIn('two.yaml', result.stdout)
            self.assertIn('floating ref', result.stdout)
            other.write_text('uses: owner/other@v2.3.4\n')
            result = run(['python3', str(script)], base, env)
            self.assertIn('resolved 2 distinct external uses refs', result.stdout)
            self.assertIn('repos/owner/other/git/ref/tags/v2.3.4', log.read_text())


if __name__ == '__main__':
    unittest.main(verbosity=2)
