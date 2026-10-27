"""Install the current sync copy and remove only Stardust's former time hooks."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

ROOT = Path("C:/OperatorDerivativeRewrite")
HERE = ROOT / "tools/stardust_sync"
STATE = ROOT / ".lake/stardust-sync"


def atomic_write(path, content):
    pending = path.with_name(path.name + '.sync-pending')
    pending.write_bytes(content)
    os.replace(pending, path)


def install():
    # Do all conflict checks before mutating anything. Preserve unrelated hooks.
    targets = []
    hook = (HERE / "pre-push").read_bytes()
    for store in (ROOT / ".git", STATE / "objects.git"):
        configured = subprocess.run(["git", "--git-dir=" + str(store), "config", "--get",
                                     "core.hooksPath"], capture_output=True, check=False)
        if configured.returncode not in (0, 1) or configured.stdout.strip():
            raise RuntimeError("Inspect existing hooksPath before installing: " + str(store))
        target = store / "hooks/pre-push"
        if target.exists() and target.read_bytes().replace(b"\r\n", b"\n") != hook.replace(b"\r\n", b"\n"):
            raise RuntimeError("Unrecognized pre-push hook must be preserved: " + str(target))
        targets.append(target)
    installed = STATE / "sync.py"
    backup = STATE / "sync.before-workday-policy.py"
    if not backup.exists():
        shutil.copyfile(installed, backup)
    atomic_write(installed, (HERE / "sync.py").read_bytes())
    for target in targets:
        if target.exists():
            target.unlink()
    receipt = {"installed_sha256": {str(installed): hashlib.sha256(installed.read_bytes()).hexdigest()},
               "removed_stardust_hooks": [str(p) for p in targets],
               "former_sync_preserved": str(backup), "scheduler_unchanged": True,
               "workday_push_restriction": False}
    (STATE / "workday-policy-removal.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    install()
