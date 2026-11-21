#!/usr/bin/env python3
"""Zero-AI-credit controller: claims low-cost RH modules, runs GitHub Actions on your fork, and posts Replay submissions."""
import argparse
import csv
import gzip
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

UPSTREAM = 'rohanarun/alpoge-rh-replay'
WORKFLOW = 'volunteer-replay.yml'
ROOT = Path(__file__).resolve().parent.parent


def gh(*args, input_text=None):
    cmd = ['gh', *args]
    res = subprocess.run(
        cmd,
        input=input_text,
        capture_output=True,
        text=True,
        encoding='utf-8',
    )
    if res.returncode != 0:
        raise RuntimeError(f"Command failed ({' '.join(cmd)}): {res.stderr.strip()}")
    return res.stdout


def load_graph():
    done = {}
    completed_path = ROOT / 'tracker/completed.tsv'
    if completed_path.exists():
        with completed_path.open(encoding='utf-8') as f:
            done = {r['id']: r['evidence'] for r in csv.DictReader(f, delimiter='\t')}

    rows = {}
    with gzip.open(ROOT / 'tracker/modules.jsonl.gz', 'rt', encoding='utf-8') as stream:
        for line in stream:
            r = json.loads(line)
            if r['id'] in done:
                r['state'] = done[r['id']]
            rows[r['id']] = r
    return rows


def fetch_busy_claims():
    from concurrent.futures import ThreadPoolExecutor
    import urllib.request

    token = gh('auth', 'token').strip()
    headers = {
        'Authorization': f'Bearer {token}',
        'Accept': 'application/vnd.github+json',
        'User-Agent': 'rh-gha-volunteer',
    }

    def fetch_page(page):
        url = f'https://api.github.com/repos/{UPSTREAM}/issues?state=open&per_page=100&page={page}'
        req = urllib.request.Request(url, headers=headers)
        with urllib.request.urlopen(req, timeout=30) as resp:
            return json.loads(resp.read().decode('utf-8'))

    busy = set()
    page_start = 1
    batch_size = 10
    while True:
        pages = range(page_start, page_start + batch_size)
        with ThreadPoolExecutor(max_workers=batch_size) as pool:
            batches = list(pool.map(fetch_page, pages))
        done_paging = False
        for items in batches:
            for item in items:
                if 'pull_request' in item:
                    continue
                m = re.fullmatch(r'Claim (M\d{6}|P\d{4})', item.get('title', ''))
                if m:
                    busy.add(m.group(1))
            if len(items) < 100:
                done_paging = True
        if done_paging:
            break
        page_start += batch_size
    return busy


def rank_candidates(rows, busy, max_closure=30):
    consumers = {mid: 0 for mid in rows}
    for r in rows.values():
        if r['state'] == 'open':
            for dep in r['imports']:
                consumers[dep] = consumers.get(dep, 0) + 1

    cands = []
    for mid, r in rows.items():
        if r['state'] != 'open' or mid in busy or r['packet'] in busy:
            continue
        if r['depth'] >= max_closure:
            continue
        seen = {mid}
        stack = list(r['imports'])
        too_big = False
        while stack:
            dep = stack.pop()
            if dep not in seen:
                seen.add(dep)
                if len(seen) > max_closure:
                    too_big = True
                    break
                stack.extend(rows[dep]['imports'])
        if not too_big:
            cands.append((len(seen), r['depth'], -consumers.get(mid, 0), mid, r['packet'], r['module'], frozenset(seen)))
    cands.sort(key=lambda x: x[:6])
    return cands


def claim_and_wait_grant(target, owner, poll_seconds=10, timeout_seconds=300):
    body = (
        f'I am working on {target}. '
        f'I will attach the input hashes, build transcript and receipt, or close this claim if I stop.'
    )
    created = json.loads(gh(
        'api', '--method', 'POST', f'repos/{UPSTREAM}/issues',
        '--input', '-',
        input_text=json.dumps({'title': f'Claim {target}', 'body': body}),
    ))
    number = created['number']
    print(f'Opened Claim {target}: https://github.com/{UPSTREAM}/issues/{number} — waiting for bot grant...', flush=True)

    deadline = time.time() + timeout_seconds
    while time.time() < deadline:
        time.sleep(poll_seconds)
        issue = json.loads(gh('api', f'repos/{UPSTREAM}/issues/{number}'))
        labels = {lbl['name'] for lbl in issue.get('labels', [])}
        comments = json.loads(gh('api', f'repos/{UPSTREAM}/issues/{number}/comments?per_page=100'))

        if 'claim-conflict' in labels or any(
            c['user']['login'] == 'github-actions[bot]' and c['body'].startswith('No grant.')
            for c in comments
        ):
            print(f'Claim {target} (#{number}) had a conflict; closing cleanly...', flush=True)
            gh('api', '--method', 'PATCH', f'repos/{UPSTREAM}/issues/{number}',
               '--input', '-', input_text=json.dumps({'state': 'closed'}))
            return None

        if 'claim-granted' in labels and any(
            c['user']['login'] == 'github-actions[bot]' and c['body'].startswith(f'Granted `{target}`.')
            for c in comments
        ):
            if issue['user']['login'].casefold() != owner.casefold():
                raise RuntimeError('Unexpected issue owner')
            print(f'Granted `{target}` on #{number}!', flush=True)
            return number

    print(f'Timed out waiting for grant on #{number}; leaving open or check manually.', file=sys.stderr)
    return None


def inspect_before_submit(number, target, owner):
    issue = json.loads(gh('api', f'repos/{UPSTREAM}/issues/{number}'))
    comments = json.loads(gh('api', f'repos/{UPSTREAM}/issues/{number}/comments?per_page=100'))
    for c in comments:
        lines = (c.get('body') or '').splitlines()
        if c['user']['login'].casefold() == owner.casefold() and lines and lines[0].strip().casefold() == 'replay submission':
            return 'already_submitted', c['html_url']
    labels = {lbl['name'] for lbl in issue.get('labels', [])}
    if issue['state'] != 'open' or 'claim-conflict' in labels or 'claim-granted' not in labels:
        return f"invalid_state:{issue['state']}:{sorted(labels)}", None
    return 'ready', None


def run_batch(fork, count, max_closure, explicit_targets=None):
    owner = json.loads(gh('api', 'user'))['login']
    print(f'Authenticated as @{owner}; using fork {fork}', flush=True)

    # Sync completed.tsv from upstream first so we don't pick newly completed tasks
    subprocess.run(['git', '-C', str(ROOT), 'fetch', '--depth', '1', 'upstream', 'main'], check=False)
    subprocess.run(['git', '-C', str(ROOT), 'checkout', 'upstream/main', '--', 'tracker/completed.tsv'], check=False)

    rows = load_graph()
    busy = fetch_busy_claims()
    cands = rank_candidates(rows, busy, max_closure=max_closure)
    if not cands and not explicit_targets:
        raise SystemExit(f'No open unclaimed modules found with closure <= {max_closure}. Increase --max-closure.')

    granted = []
    idx = 0
    wanted = list(explicit_targets) if explicit_targets else []

    while len(granted) < count:
        if wanted:
            target = wanted.pop(0)
        else:
            if idx >= len(cands):
                break
            cl_size, depth, neg_cons, target, pkt, mod, _ = cands[idx]
            idx += 1
            print(f'Candidate {target} (packet {pkt}, depth {depth}, total closure {cl_size}, consumers {-neg_cons}): {mod}', flush=True)

        issue_num = claim_and_wait_grant(target, owner)
        if issue_num is not None:
            granted.append((target, issue_num))

    if not granted:
        raise SystemExit('Could not secure any grants.')

    assignments_arg = ' '.join(f'{t}:{n}' for t, n in granted)
    existing_ids = {
        r['databaseId']
        for r in json.loads(gh('run', 'list', '-R', fork, '-w', WORKFLOW, '-L', '10', '--json', 'databaseId'))
    }
    print(f'Dispatching {WORKFLOW} on {fork} with assignments: {assignments_arg}', flush=True)
    gh('workflow', 'run', WORKFLOW, '-R', fork, '-f', f'assignments={assignments_arg}')

    run_id = None
    for _ in range(30):
        time.sleep(4)
        runs = json.loads(gh('run', 'list', '-R', fork, '-w', WORKFLOW, '-L', '10',
                             '--json', 'databaseId,status,createdAt,url'))
        for r in runs:
            if r['databaseId'] not in existing_ids:
                run_id = r['databaseId']
                print(f"Tracking workflow run #{run_id}: {r['url']}", flush=True)
                break
        if run_id:
            break
    if not run_id:
        raise RuntimeError('Could not locate triggered workflow run')

    while True:
        info = json.loads(gh('run', 'view', str(run_id), '-R', fork, '--json', 'status,conclusion,url'))
        print(f"  Run #{run_id} status={info['status']} conclusion={info.get('conclusion')}", flush=True)
        if info['status'] == 'completed':
            if info.get('conclusion') != 'success':
                raise RuntimeError(f"Workflow run failed ({info.get('conclusion')}): {info['url']}")
            break
        time.sleep(25)

    with tempfile.TemporaryDirectory() as tmp:
        gh('run', 'download', str(run_id), '-R', fork, '-n', f'replay-submissions-{run_id}', '-D', tmp)
        results = json.loads((Path(tmp) / 'results.json').read_text(encoding='utf-8'))

    for item in results:
        target = item['target']
        number = item['issue']
        if item['exit_code'] != 0:
            print(f"Skipping auto-submit for failed target {target} (#{number})", file=sys.stderr)
            continue
        state, existing_url = inspect_before_submit(number, target, owner)
        if state == 'already_submitted':
            print(f'Already submitted {target} (#{number}): {existing_url}', flush=True)
            continue
        if state != 'ready':
            print(f'Grant state changed for {target} (#{number}): {state}', file=sys.stderr)
            continue
        posted = json.loads(gh(
            'api', '--method', 'POST', f'repos/{UPSTREAM}/issues/{number}/comments',
            '--input', '-',
            input_text=json.dumps({'body': item['comment_body']}),
        ))
        print(f"Posted Replay submission for {target}: {posted['html_url']}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fork', default='Sethumathavanpk/alpoge-rh-replay', help='Your fork OWNER/REPO')
    parser.add_argument('--count', type=int, default=1, help='Number of modules to claim & build in this run')
    parser.add_argument('--max-closure', type=int, default=30, help='Max transitive project-module closure size')
    parser.add_argument('--list-only', action='store_true', help='Only list top low-cost open candidates')
    parser.add_argument('--target', action='append', help='Explicit module/packet ID(s) to claim')
    args = parser.parse_args()

    if args.list_only:
        rows = load_graph()
        busy = fetch_busy_claims()
        cands = rank_candidates(rows, busy, max_closure=args.max_closure)
        print(f'Found {len(cands)} open unclaimed modules with closure <= {args.max_closure}:')
        for cl_size, depth, neg_cons, mid, pkt, mod, _ in cands[:20]:
            print(f'  {mid} (packet {pkt}, depth={depth}, closure={cl_size}, consumers={-neg_cons})  {mod}')
        return

    run_batch(args.fork, args.count, args.max_closure, args.target)


if __name__ == '__main__':
    main()
