# Audited GitHub checkpoint synchronization

## Current policy — public repository and user-controlled visibility

The user explicitly designated QuijoticResearch/OperatorDerivativeRewrite PUBLIC.
The research agent, sync script and Windows scheduled task must NEVER change
repository visibility. Earlier PRIVATE-visibility requirements in historical
sections and checkpoint records are superseded. The sync script reads the
GitHub repository identity and push permission before work, immediately before
a push, and after remote verification. It records the observed visibility but
does not require private visibility or mutate visibility. Normal audited
commits and automatic pushes are allowed while the repository is PUBLIC.

The existing Windows task retains its historical name, Project Stardust
Private GitHub Sync, and its 30-minute trigger; no duplicate task is created.
Both authorized main and research branches remain. Exact-commit approval,
full-build/axiom/type/source gates, complete new-history secret scanning,
suspicious-path refusal, atomic fast-forward no-force pushes and exact remote
ref verification remain mandatory. ResearchSources stays uncommitted. No
agent or script may use GitHub visibility-editing APIs or commands. The
weekday intraday push restriction remains lifted.

## Public-policy implementation check

The installed script is byte-identical to tools/stardust_sync/sync.py. Its
read-only repository-access function uses GitHub GET for exact repository
identity and push permission; it neither gates on visibility nor issues any
visibility-changing request. The current no-network policy tests cover PUBLIC
and private metadata, identity/permission refusal, installed-script identity,
and absent old time-policy hooks. A search of tracked executable scripts,
GitHub workflows, both Stardust scheduled-task launchers and all scheduled
task actions found no persisted operation that changes repository visibility;
there was nothing to disable. The preserved historical sync copy is inactive.
The 30-minute trigger and two backup branches were retained.

The first end-to-end PUBLIC sync under this policy verified both main and
codex/stardust-pseudoprocess-calculus at mathematical commit
084d12e1f8a0a129585b0976f527527c167206de. The receipt recorded
visibility=public and private=false, and an independent GitHub query still
reported PUBLIC afterward. Any earlier agent attempts to restore PRIVATE
visibility predate the user's explicit policy and must never recur.

## Historical October27 intraday-policy amendment — superseded by public visibility

The user explicitly removed the Monday–Friday09:00–17:00 America/New_York
external-push restriction and requested immediate Git synchronization.
Audited local commits may now sync at any hour. The prior workday section
below is retained as a historical implementation record and is superseded.
Install the current versioned script with `tools/stardust_sync/install.py`;
it removes only the matching Stardust time-policy pre-push hooks from the
live checkout and isolated Git store. The old `push_policy.py` and `pre-push`
files remain as inactive historical references, not installed guards.

The existing 30-minute Windows task, exact-commit approval, private-repository
identity/permissions checks, full new-history secret scan, fast-forward and
atomic no-force push, and post-push remote-ref verification remain unchanged.
Synchronization failure must remain a failure; never report a queued or failed
commit as remotely backed up. ResearchSources and unaudited work stay out of
the commit set. The installed scheduled script is updated in place without
creating another task. Reinstall after restoring the repository or replacing
either Git store, and confirm both live pre-push hooks are absent before an
intraday push. If an unrelated hook exists, preserve it and investigate.

The current policy was checked against a PRIVATE GitHub repository with push
permission before installation. The exact remote `main` and research branch
tips must be verified after synchronization. Run the current no-network guard
checks with `python -X utf8 tools/stardust_sync/test_policy.py`. The former
clock-boundary test suite is preserved as
`tools/stardust_sync/historical_workday_policy_tests.py` for historical review.

## Historical workday push policy — effective October26,2026; superseded October27

External pushes are prohibited Monday–Friday from **09:00 inclusive until
17:00 exclusive, America/New_York**, unless the user explicitly authorizes an
exception. Python `zoneinfo.ZoneInfo('America/New_York')` supplies DST rules;
this is independent of the Windows display time zone. Weekends and all other
hours remain eligible. There is no unattended exception flag or clock override.

The existing 30-minute Windows task is unchanged. It records `status: queued`
and `backup_verified: false` during restricted hours, preserving approvals and
`last-success.json`; this is a successful policy deferral (task exit0), NOT a
successful backup. Local refs are recorded as candidates, not certified remote
tips. The next eligible scheduled run uses the existing privacy checks, secret
scan, fast-forward/atomic push and exact remote verification. Failures retain
exit1 and `status: failure`, and the task retries at its next invocation.

Enforcement is at two levels: the synchronization script checks at entry AND
immediately before Git push, and pre-push hooks in BOTH `.git/hooks/pre-push`
and `.lake/stardust-sync/objects.git/hooks/pre-push` check the live clock for
any external destination. A run crossing 09:00 before admission is deferred;
an already admitted push is allowed to finish, with no kill timer at 09:00.
Time-zone verification failure refuses the push. Local filesystem Git transfers
remain permitted by the hooks; network/unknown destinations are treated as
external. Deliberately bypassing hooks/configuration is not authorized. Hooks
are a local workflow safeguard, not a server-side access-control boundary.

Continue mathematical research and ALL verification normally. Commit locally
and create the exact-commit receipt as usual. Record **LOCAL AUDIT COMPLETE;
REMOTE SYNC QUEUED**, with the intended commit/ref targets. A deferred backup
must not block proof work or an otherwise fully audited campaign transition.
This timing amendment supersedes older instructions requiring immediate PRIVATE
remote closure; it changes no audit requirements or research priorities. After
an eligible successful sync, record the actual verified remote tips; a later
verified descendant can cover an earlier queued checkpoint without rewriting it.

Versioned implementation: `tools/stardust_sync/{sync.py,push_policy.py,pre-push}`.
`install.py` copies the canonical sync script into the existing scheduled path
and installs the hooks, refusing conflicting hooks/hooksPath; it preserves the
original sync script as `.lake/stardust-sync/sync.before-workday-policy.py`.
It does not register another task or alter its trigger, account, lock or launcher.
Reinstall after restoring the repository or replacing either Git object store:

```powershell
& 'C:/Users/ramir/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe' -X utf8 tools/stardust_sync/install.py
& 'C:/Users/ramir/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe' -X utf8 tools/stardust_sync/test_policy.py
```

The Windows runtime currently has the IANA time-zone database; missing data
fails closed. Tests cover exact hour boundaries, weekdays/weekends, both DST
offsets, transport refusal, queue status, clock failure and an actual local Git
hook/ref-update fixture. Tests never contact an external test repository.
Rollback of an implementation defect must retain the time restriction: disable
the sync task first, preserve pending receipts, repair/reinstall the guards,
then re-enable it. Restoring the unguarded original is NOT an authorized policy
rollback. Only the user may lift the workday policy.

## Current operational procedure

Windows Task Scheduler runs **Project Stardust Private GitHub Sync** every 30 minutes,
independently of Codex. It uses the signed-in Windows account's existing `gh` keyring.
Windows must be running and that account signed in; no Codex window or agent is needed.
Missed runs are eligible to run when the scheduler becomes available. No password/token
is saved in task files. The task runs at limited privilege and low priority.

Repository: https://github.com/QuijoticResearch/OperatorDerivativeRewrite (PUBLIC by user decision).
The initial archive remains on `backup/stardust-2026-10-18`. `main` contains audited
research only. Existing branch names and tags are preserved. The scheduler never makes
commits, runs Lean builds, checks out files, changes the research index, force-pushes,
rewrites history, or deletes remote refs. Divergence/tag replacement, failed identity/permission checks, failed secret scans,
or failed remote verification produce a failing task result.

Implementation and state: `C:\OperatorDerivativeRewrite\.lake\stardust-sync`.
Keep this directory and the referenced portable Gitleaks executable when cleaning caches.
`last-run.json` records the latest result; `last-success.json` records verified remote
commit IDs; `last-task.log` records launcher output. The task rechecks repository identity and push permission immediately before
pushing, pushes atomically without force, and rereads remote refs afterward.
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
