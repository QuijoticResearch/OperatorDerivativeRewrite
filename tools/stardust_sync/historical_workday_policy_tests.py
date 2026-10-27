"""Boundary/DST tests and transport-spy checks; never contact an external remote."""
from datetime import datetime
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import push_policy as policy
import sync


class PolicyTests(unittest.TestCase):
    def test_eastern_boundaries_and_dst(self):
        cases = [
            ("2026-10-26T12:59:59+00:00", False),
            ("2026-10-26T13:00:00+00:00", True),
            ("2026-10-26T20:59:59+00:00", True),
            ("2026-10-26T21:00:00+00:00", False),
            ("2026-10-30T21:00:00+00:00", False),
            ("2026-10-31T16:00:00+00:00", False),
            ("2026-11-01T16:00:00+00:00", False),
            ("2026-11-02T13:59:59+00:00", False),
            ("2026-11-02T14:00:00+00:00", True),
            ("2026-11-02T21:59:59+00:00", True),
            ("2026-11-02T22:00:00+00:00", False),
            ("2027-03-15T13:00:00+00:00", True),
            ("2027-03-15T21:00:00+00:00", False),
        ]
        for instant, expected in cases:
            with self.subTest(instant=instant):
                self.assertEqual(policy.restricted(datetime.fromisoformat(instant)), expected)

    def test_transports(self):
        at = datetime.fromisoformat("2026-10-26T16:00:00+00:00")
        for remote in ("https://github.com/x/y", "git@example.org:x/y", "ssh://x/y",
                       "//server/repo", "\\\\server\\repo", "file://server/repo", "unknown"):
            self.assertTrue(policy.blocked(remote, at), remote)
        for remote in ("C:/local/repo", "C:\\local\\repo", "/tmp/local", "../repo", "file:///C:/repo"):
            self.assertFalse(policy.blocked(remote, at), remote)

    def test_restricted_sync_no_network_and_not_success(self):
        with patch.object(policy, 'restricted', return_value=True), \
             patch.object(sync, 'privacy', side_effect=AssertionError("network forbidden")), \
             patch.object(sync, 'git', return_value=b'refs/heads/research abc\n') as git:
            result = sync.sync()
            self.assertEqual(result['status'], 'queued')
            self.assertFalse(result['backup_verified'])
            self.assertEqual(git.call_count, 1)
            self.assertEqual(git.call_args.args[0], 'for-each-ref')

    def test_push_rechecked_after_scanning_and_other_remotes(self):
        with patch.object(policy, 'restricted', return_value=True), \
             patch.object(sync, 'run', side_effect=AssertionError("transport forbidden")):
            for url in ('https://github.com/x/y', 'ssh://another.example/repo'):
                with self.assertRaises(sync.PushDeferred):
                    sync.git('push', '--atomic', url, 'abc:refs/heads/main')

    def test_allowed_push_is_not_terminated_at_boundary(self):
        with patch.object(policy, 'restricted', return_value=False) as clock, \
             patch.object(sync, 'run', return_value=b'ok') as run:
            self.assertEqual(sync.git('push', '--atomic', sync.URL), b'ok')
            self.assertEqual(clock.call_count, 1)
            self.assertEqual(run.call_count, 1)

    def test_timezone_failure_does_not_reach_transport(self):
        with patch.object(policy, 'restricted', side_effect=RuntimeError('tz failure')), \
             patch.object(sync, 'run', side_effect=AssertionError("transport forbidden")):
            with self.assertRaises(RuntimeError):
                sync.git('push', sync.URL)

    def test_actual_git_hook_blocks_then_allows_local_fixture(self):
        # Exercise an actual Git push/ref update without any external connection.
        # The fixture hook substitutes only a test-clock launcher for production's
        # live-clock launcher; it imports the SAME production policy implementation.
        here = Path(__file__).resolve().parent
        with tempfile.TemporaryDirectory(prefix='policy-test-', dir=sync.STATE) as folder:
            base = Path(folder)
            src, dest = base/'source', base/'remote.git'
            def git(*args):
                return subprocess.run([sync.GIT, *map(str, args)], capture_output=True, text=True)
            self.assertEqual(git('init', src).returncode, 0)
            self.assertEqual(git('init', '--bare', dest).returncode, 0)
            self.assertEqual(git('-C', src, '-c', 'user.name=Policy Test', '-c',
                                 'user.email=policy-test@localhost', 'commit', '--allow-empty',
                                 '-m', 'Local policy fixture').returncode, 0)
            launcher = base/'check.py'
            clock_file = base/'clock'
            clock_file.write_text('2026-10-26T13:00:00+00:00')
            launcher.write_text(
                'import sys\nfrom datetime import datetime\nfrom pathlib import Path\n'
                f'sys.path.insert(0, {str(here)!r})\nimport push_policy as p\n'
                f'at=datetime.fromisoformat(Path({str(clock_file)!r}).read_text())\n'
                'original=p.restricted\np.restricted=lambda instant=None: original(at)\n'
                'sys.argv=[sys.argv[0], "--remote", "https://external.invalid/repo"]\n'
                'sys.exit(p.main())\n', encoding='utf-8')
            hook = (here/'pre-push').read_text().replace(
                'C:/OperatorDerivativeRewrite/tools/stardust_sync/push_policy.py', launcher.as_posix())
            (src/'.git/hooks/pre-push').write_bytes(hook.encode())
            denied = git('-C', src, 'push', dest, 'HEAD:refs/heads/check')
            self.assertNotEqual(denied.returncode, 0)
            self.assertIn('External push queued', denied.stderr)
            self.assertNotEqual(git('--git-dir='+str(dest), 'rev-parse', '--verify',
                                    'refs/heads/check').returncode, 0)
            clock_file.write_text('2026-10-26T21:00:00+00:00')
            allowed = git('-C', src, 'push', dest, 'HEAD:refs/heads/check')
            self.assertEqual(allowed.returncode, 0, allowed.stderr)
            self.assertEqual(git('-C', src, 'rev-parse', 'HEAD').stdout,
                             git('--git-dir='+str(dest), 'rev-parse', 'refs/heads/check').stdout)


if __name__ == '__main__':
    unittest.main(verbosity=2)
