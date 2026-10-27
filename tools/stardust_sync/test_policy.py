"""Current private-sync guard tests; no network or Git mutation."""
import json
from pathlib import Path
import unittest
from unittest.mock import patch

import push_policy as historical_time_policy
import sync


class CurrentSyncPolicyTests(unittest.TestCase):
    def test_intraday_clock_does_not_defer_git_push(self):
        with patch.object(historical_time_policy, 'restricted', return_value=True), \
             patch.object(sync, 'run', return_value=b'') as run:
            sync.git('push', '--atomic', '--no-force', sync.URL, 'a:refs/heads/main')
            command = run.call_args.args[0]
            self.assertIn('push', command)
            self.assertIn('--atomic', command)
            self.assertIn('--no-force', command)

    def test_private_identity_and_permission_still_required(self):
        valid = {'full_name': 'QuijoticResearch/OperatorDerivativeRewrite',
                 'private': True, 'visibility': 'private',
                 'permissions': {'push': True}}
        with patch.object(sync, 'run', return_value=json.dumps(valid).encode()):
            sync.privacy()
        for change in ({'private': False}, {'visibility': 'public'},
                       {'permissions': {'push': False}}, {'full_name': 'other/repo'}):
            with self.subTest(change=change):
                with patch.object(sync, 'run', return_value=json.dumps(valid | change).encode()):
                    with self.assertRaises(RuntimeError):
                        sync.privacy()

    def test_installed_sync_and_removed_time_hooks(self):
        root = Path('C:/OperatorDerivativeRewrite')
        self.assertEqual((root/'tools/stardust_sync/sync.py').read_bytes(),
                         (root/'.lake/stardust-sync/sync.py').read_bytes())
        self.assertFalse((root/'.git/hooks/pre-push').exists())
        self.assertFalse((root/'.lake/stardust-sync/objects.git/hooks/pre-push').exists())


if __name__ == '__main__':
    unittest.main()
