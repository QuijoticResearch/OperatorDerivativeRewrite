"""Independent, non-destructive checkpoint backup. Repository visibility is user-controlled."""
import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path('C:/OperatorDerivativeRewrite')


STATE = ROOT / '.lake/stardust-sync'
REPO = STATE / 'objects.git'
URL = 'https://github.com/QuijoticResearch/OperatorDerivativeRewrite.git'
API = '/repos/QuijoticResearch/OperatorDerivativeRewrite'
GIT = 'C:/Program Files/Git/cmd/git.exe'
GH = 'C:/Program Files/GitHub CLI/gh.exe'
SCANNER = ROOT / '.lake/stardust-github-backup-20261018/tools/gitleaks/gitleaks.exe'
ENV = dict(os.environ, GIT_TERMINAL_PROMPT='0', GH_PROMPT_DISABLED='1', GCM_INTERACTIVE='never')
ENV['PATH'] = str(Path(GH).parent) + os.pathsep + ENV.get('PATH', '')


def run(args, data=None, timeout=240):
    p = subprocess.run([str(x) for x in args], input=data, stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE, env=ENV, cwd=ROOT, timeout=timeout)
    if p.returncode:
        # Do not copy arbitrary remote responses, commit content or credentials into logs.
        raise RuntimeError(f'{Path(args[0]).name} {args[1]} failed (exit {p.returncode})')
    return p.stdout


def git(*args, repo=REPO):
    return run([GIT, '--git-dir=' + str(repo), '-c', 'credential.helper=', '-c',
                'credential.helper=!gh auth git-credential', '-c', 'pack.threads=2', *args])


def now():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def save(path, value):
    temp = path.with_suffix('.tmp')
    temp.write_text(json.dumps(value, indent=2) + '\n', encoding='utf-8')
    os.replace(temp, path)


def repository_access():
    # Read-only identity and permission check. Visibility is exclusively user-controlled.
    info = json.loads(run([GH, 'api', API]))
    if info.get('full_name', '').lower() != 'quijoticresearch/operatorderivativerewrite':
        raise RuntimeError('Repository identity mismatch')
    if not info.get('permissions', {}).get('push'):
        raise RuntimeError('GitHub push permission unavailable')
    return info


def remote_refs():
    return {ref: oid for oid, ref in (line.split() for line in
            git('ls-remote', '--refs', URL).decode().splitlines())}


def ancestor(a, b):
    p = subprocess.run([GIT, '--git-dir=' + str(REPO), 'merge-base', '--is-ancestor', a, b],
                       capture_output=True, env=ENV, timeout=30)
    if p.returncode not in (0, 1):
        raise RuntimeError('Cannot verify fast-forward ancestry')
    return p.returncode == 0


def approve(args):
    """Record the research agent's completed audit, never run a build or make a commit."""
    src = ROOT / '.git'
    head = git('rev-parse', args.commit, repo=src).decode().strip()
    if git('rev-parse', 'HEAD', repo=src).decode().strip() != head:
        raise RuntimeError('Approve the exact current checkpoint only')
    if git('diff', '--name-only', 'HEAD', repo=src).strip():
        raise RuntimeError('Tracked working tree/index must be clean at audit approval')
    build = Path(args.build_log).resolve()
    audit = Path(args.audit_log).resolve()
    manifest = json.loads(Path(args.manifest).read_text(encoding='utf-8-sig'))
    if not re.search(r'Build completed successfully \(\d+ jobs\)\.', build.read_text(encoding='utf-8')):
        raise RuntimeError('Full-build success marker missing')
    text = audit.read_text(encoding='utf-8')
    match = re.search(r'AUDIT PASSED: (\d+) declarations; only propext, Classical.choice, Quot.sound', text)
    if not match or re.search(r'sorryAx|AUDIT FAILED|^error:', text, re.M):
        raise RuntimeError('Standard-axiom audit success required')
    if not args.public_types_reviewed:
        raise RuntimeError('Public theorem types must be reviewed before approval')
    expected = {k.replace('\\', '/'): v.lower() for k, v in manifest['foundation_and_root_sha256'].items()}
    entries = git('ls-tree', '-r', '-z', head, repo=src).split(b'\0')
    sources = {}
    for entry in entries:
        if not entry:
            continue
        meta, path = entry.split(b'\t', 1)
        path = path.decode()
        if path == 'OperatorDerivativeRewrite.lean' or (path.startswith('Foundation/') and path.endswith('.lean')):
            sources[path] = meta.split()[2].decode()
    if set(sources) != set(expected):
        raise RuntimeError('Audit source manifest must cover every committed Foundation/root Lean source')
    # Batch reads avoid loading/building Lean or modifying the research checkout.
    data = git('cat-file', '--batch', repo=src) if not sources else run(
        [GIT, '--git-dir=' + str(src), 'cat-file', '--batch'],
        data=('\n'.join(sources.values()) + '\n').encode())
    offset = 0
    for path in sources:
        end = data.index(b'\n', offset)
        n = int(data[offset:end].split()[2]); offset = end + 1
        blob = data[offset:offset+n]; offset += n + 1
        working = (ROOT/path).read_bytes()
        if hashlib.sha256(working).hexdigest() != expected[path]:
            raise RuntimeError('Working Lean source differs from audited manifest: ' + path)
        # Git's Windows checkout conversion may use CRLF while the stored blob uses LF.
        if blob != working and blob != working.replace(b'\r\n', b'\n'):
            raise RuntimeError('Committed Lean source differs from audited source: ' + path)
    receipt = {'commit': head, 'tree': git('rev-parse', head + '^{tree}', repo=src).decode().strip(),
               'approved_utc': now(), 'full_build_passed': True, 'axiom_audit_passed': True,
               'public_types_reviewed': True, 'declarations': int(match[1]), 'lean_sources': len(sources),
               'evidence': {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in (build, audit, Path(args.manifest))}}
    save(STATE / 'approvals' / (head + '.json'), receipt)
    print('Audited checkpoint approved: ' + head)


def scan(tips, remote):
    revs = list(set(tips)) + ['--not'] + list(set(remote.values()))
    commits = git('rev-list', *revs).decode().splitlines()
    if not commits:
        return 0
    if not SCANNER.is_file():
        raise RuntimeError('Secret scanner missing; refusing new content')
    objects = git('rev-list', '--objects', *revs).decode().splitlines()
    bad = re.compile(r'(^|/)(\.lake|node_modules|__pycache__|build|target|\.venv)(/|$)|\.(olean|ilean|pyc|exe|dll|obj)$|(^|/)(\.env(?:\..*)?|id_rsa|id_ed25519|credentials)$|\.(pem|pfx|p12|key)$', re.I)
    if any(' ' in x and bad.search(x.split(' ', 1)[1]) for x in objects):
        raise RuntimeError('Artifact or credential-like filename in new committed history; manual review required')
    with tempfile.TemporaryDirectory(prefix='secret-scan-', dir=STATE) as temp:
        folder = Path(temp).resolve()
        assert folder.parent == STATE.resolve()
        # Inspect complete new blobs/commit messages, including merge-only content.
        p = subprocess.Popen([GIT, '--git-dir=' + str(REPO), 'cat-file', '--batch'],
                             stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, env=ENV)
        try:
            for line in objects:
                oid = line.split(' ', 1)[0]
                p.stdin.write((oid + '\n').encode()); p.stdin.flush()
                header = p.stdout.readline().split(); size = int(header[2])
                blob = p.stdout.read(size)
                if len(blob) != size or p.stdout.read(1) != b'\n':
                    raise RuntimeError('Incomplete Git object read')
                if header[1] in (b'blob', b'commit'):
                    (folder / (oid + '.txt')).write_bytes(blob)
            p.stdin.close()
            if p.wait(timeout=30):
                raise RuntimeError('Git object scan failed')
        finally:
            if p.poll() is None:
                p.kill(); p.wait()
        run([SCANNER, 'dir', folder, '--ignore-gitleaks-allow', '--redact=100', '--no-banner'])
    return len(commits)


def sync():
    repository_access()
    if not REPO.exists():
        run([GIT, '-c', 'credential.helper=', '-c', 'credential.helper=!gh auth git-credential',
             'clone', '--mirror', URL, REPO])
    remote = remote_refs()
    lines = git('for-each-ref', '--format=%(refname) %(objectname)', 'refs/heads/', 'refs/tags/', repo=ROOT/'.git').decode().splitlines()
    local = dict(line.split() for line in lines)
    tips = set(local.values()) | set(remote.values())
    # Only this isolated object store is written; the live research index is never touched.
    for origin, values in ((str(ROOT), set(local.values())), (URL, set(remote.values()))):
        missing = [oid for oid in values if subprocess.run([GIT, '--git-dir='+str(REPO), 'cat-file', '-e', oid], capture_output=True).returncode]
        if missing:
            git('fetch', '--no-tags', '--no-write-fetch-head', origin, *missing)
    desired = {ref: oid for ref, oid in local.items() if ref != 'refs/heads/main'}
    approved = []
    for path in (STATE/'approvals').glob('*.json'):
        a = json.loads(path.read_text())
        oid = a['commit']
        if not all(a.get(k) is True for k in ('full_build_passed','axiom_audit_passed','public_types_reviewed')):
            continue
        if not any(ancestor(oid, tip) for ref, tip in local.items() if ref.startswith('refs/heads/')):
            continue
        if git('rev-parse', oid+'^{tree}').decode().strip() != a['tree']:
            raise RuntimeError('Audit receipt tree mismatch')
        if 'refs/heads/main' not in remote or ancestor(remote['refs/heads/main'], oid):
            approved.append(oid)
    if approved:
        best = approved[0]
        for oid in approved[1:]:
            if ancestor(best, oid): best = oid
            elif not ancestor(oid, best): raise RuntimeError('Audited checkpoints diverge; refusing main promotion')
        desired['refs/heads/main'] = best
    changes = {ref: oid for ref, oid in desired.items() if remote.get(ref) != oid}
    for ref, oid in changes.items():
        if ref in remote and (ref.startswith('refs/tags/') or not ancestor(remote[ref], oid)):
            raise RuntimeError('Non-fast-forward or changed tag refused: '+ref)
    scanned = scan(changes.values(), remote) if changes else 0
    repository_access()  # recheck identity and permission immediately before push
    if changes:
        git('push', '--atomic', '--no-force', URL, *[oid+':'+ref for ref, oid in changes.items()])
    after = remote_refs()
    if any(after.get(ref) != oid for ref, oid in desired.items()):
        raise RuntimeError('Remote commit verification failed')
    info = repository_access()
    result = {'status':'success', 'time_utc':now(), 'private':info.get('private'),
              'visibility':info.get('visibility'), 'url':URL,
              'pushed_refs':changes, 'verified_refs':desired, 'new_commits_secret_scanned':scanned,
              'main_policy':'exact-commit audit approval required; all pushes fast-forward; no commits or deletions'}
    save(STATE/'last-success.json', result)
    return result


def main():
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest='command', required=True)
    sub.add_parser('sync')
    a = sub.add_parser('approve')
    for flag in ('commit','manifest','build-log','audit-log'): a.add_argument('--'+flag, required=True)
    a.add_argument('--public-types-reviewed', action='store_true')
    args = parser.parse_args()
    if args.command == 'approve':
        approve(args); return
    try:
        # Task Scheduler also uses IgnoreNew; this lock covers manual concurrent launches.
        import msvcrt
        with (STATE/'run.lock').open('a+b') as lock:
            lock.seek(0); lock.write(b'0'); lock.flush(); lock.seek(0)
            try: msvcrt.locking(lock.fileno(), msvcrt.LK_NBLCK, 1)
            except OSError: return
            result = sync()
            save(STATE/'last-run.json', result)
            print('Synchronization verified')
    except Exception as e:
        result = {'status':'failure','time_utc':now(),'error':str(e)}
        save(STATE/'last-run.json', result)
        print(json.dumps(result), file=sys.stderr)
        sys.exit(1)


if __name__ == '__main__': main()
