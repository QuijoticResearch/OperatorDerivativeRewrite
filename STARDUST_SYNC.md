# Independent private GitHub checkpoint synchronization

Windows Task Scheduler runs **Project Stardust Private GitHub Sync** every 30 minutes,
independently of Codex. It uses the signed-in Windows account's existing `gh` keyring.
Windows must be running and that account signed in; no Codex window or agent is needed.
Missed runs are eligible to run when the scheduler becomes available. No password/token
is saved in task files. The task runs at limited privilege and low priority.

Repository: https://github.com/QuijoticResearch/OperatorDerivativeRewrite (private).
The initial archive remains on `backup/stardust-2026-10-18`. `main` contains audited
research only. Existing branch names and tags are preserved. The scheduler never makes
commits, runs Lean builds, checks out files, changes the research index, force-pushes,
rewrites history, or deletes remote refs. Divergence/tag replacement, failed privacy
checks, failed secret scans, or failed remote verification produce a failing task result.

Implementation and state: `C:\OperatorDerivativeRewrite\.lake\stardust-sync`.
Keep this directory and the referenced portable Gitleaks executable when cleaning caches.
`last-run.json` records the latest result; `last-success.json` records verified remote
commit IDs; `last-task.log` records launcher output. The task verifies privacy immediately
before pushing, pushes atomically without force, and rereads remote refs afterward.
New committed blobs/messages are scanned for credentials; suspicious paths stop syncing.
These checks supplement research review, rather than guaranteeing every secret format is detectable.

## At each audited research checkpoint

Finish the existing full-build, axiom-audit, public-type inspection, manuscript integrity,
ledger, and Git checkpoint procedures first. Never approve unfinished work. After the
audited commit exists and the tracked tree/index is clean, record an exact-commit receipt:

```powershell
& 'C:/Users/ramir/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe' -X utf8 `
  .lake/stardust-sync/sync.py approve `
  --commit <FULL_COMMIT_ID> `
  --manifest .lake/<checkpoint-working-manifest>.json `
  --build-log .lake/<successful-full-build>.log `
  --audit-log .lake/<successful-root-axiom-audit>.log `
  --public-types-reviewed
```

The manifest must contain `foundation_and_root_sha256` covering all committed
Foundation/root Lean sources, as in checkpoint 1081. Approval checks source bytes against
that manifest and the committed tree (allowing Git CRLF/LF checkout conversion), success
markers, and clean tracked state. The research agent attests that logs belong to this
checkpoint and public theorem types were inspected. It is not a replacement for those
proof/audit procedures. Receipt creation neither commits nor pushes anything.

At the next scheduled run, the newest approved descendant advances remote `main` by
fast-forward. Committed research branches/tags are backed up even while `main` awaits an
approval. An unapproved local `main` is withheld. Keep archive/draft branches distinct
from mathematical certification. Do not reset a divergent ref to make synchronization pass.

To check operation:

```powershell
Get-ScheduledTaskInfo -TaskName 'Project Stardust Private GitHub Sync'
Get-Content .lake/stardust-sync/last-run.json
```

To disable it, use `Disable-ScheduledTask` with that exact task name. Future audit
receipts are part of checkpoint closure; they do not interrupt active IBM proof work.
