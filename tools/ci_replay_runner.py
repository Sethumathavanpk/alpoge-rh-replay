#!/usr/bin/env python3
"""Runs inside the GitHub Actions Ubuntu 24.04 runner in two isolated phases: build (no token) and publish."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'tracker'))

import replay_evidence as evidence  # noqa: E402
import tasks  # noqa: E402
import worker_build  # noqa: E402


def parse_pairs(raw):
    raw_pairs = raw.split()
    if not raw_pairs:
        raise SystemExit('No TARGET:ISSUE assignments provided')
    pairs = []
    for item in raw_pairs:
        m = re.fullmatch(r'(M\d{6}|P\d{4}):(\d+)', item.strip())
        if not m:
            raise SystemExit(f'Invalid assignment token: {item!r} (expected TARGET:ISSUE)')
        pairs.append((m.group(1), int(m.group(2))))
    return pairs


def phase_build(work_dir: Path, out_summary: Path, pairs):
    checkout = work_dir / 'lean'
    receipts_root = work_dir / 'receipts'
    out_summary.mkdir(parents=True, exist_ok=True)
    rows = {r['module']: r for r in tasks.module_rows()}

    built_manifest = []
    failures = 0

    for target, issue_num in pairs:
        print(f'=== Building {target} for {tasks.repo}#{issue_num} ===', flush=True)
        out_dir = receipts_root / f'{target}-{issue_num}'
        code = worker_build.build(target, checkout, out_dir)
        receipt_path = out_dir / 'receipt.json'
        log_path = out_dir / 'build.log'

        if code != 0:
            failures += 1
            log_excerpt = ''
            if log_path.exists():
                lines = log_path.read_text(errors='replace').splitlines()
                log_excerpt = '\n'.join(lines[:60])
            built_manifest.append({
                'target': target,
                'issue': issue_num,
                'exit_code': code,
                'error_excerpt': log_excerpt,
            })
            print(f'Build failed for {target} with exit code {code}', file=sys.stderr, flush=True)
            continue

        targets = tasks.select(rows.values(), target)
        verified = evidence.verify(out_dir, targets, rows, checkout)
        receipt = json.loads(receipt_path.read_text())

        # Also run target-level leanchecker check on freshly compiled modules
        kernel_check_seconds = None
        if not (out_dir / evidence.REPLAY_FILE).exists():
            _, launcher, env = evidence.checkout_info(checkout)
            k_cmd = ['lake', 'env', 'leanchecker', '--verbose', *[r['module'] for r in targets]]
            t0 = time.monotonic()
            k_res = subprocess.run(
                [*launcher, *k_cmd],
                env=dict(env, LEAN_NUM_THREADS='1'),
                cwd=checkout,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
            )
            kernel_check_seconds = round(time.monotonic() - t0, 2)
            if k_res.returncode != 0:
                failures += 1
                built_manifest.append({
                    'target': target,
                    'issue': issue_num,
                    'exit_code': k_res.returncode,
                    'error_excerpt': k_res.stdout[:2000],
                })
                print(f'Kernel check failed for {target}', file=sys.stderr, flush=True)
                continue
            verified = evidence.verify(out_dir, targets, rows, checkout)

        built_manifest.append({
            'target': target,
            'issue': issue_num,
            'exit_code': 0,
            'out_dir': str(out_dir),
            'verified': verified,
            'receipt': receipt,
            'kernel_check_seconds': kernel_check_seconds,
        })
        print(f'Build & verification passed for {target}', flush=True)

    (out_summary / 'build_manifest.json').write_text(json.dumps(built_manifest, indent=2) + '\n', encoding='utf-8')
    if failures and len(built_manifest) == failures:
        raise SystemExit(1)


def publish_release(fork, upstream, target, issue_num, files):
    tag = f'replay-{target}-issue-{issue_num}'
    route = f'repos/{fork}/releases/tags/{tag}'
    probe = subprocess.run(['gh', 'api', route], capture_output=True, text=True)
    if probe.returncode != 0:
        if '(HTTP 404)' not in probe.stderr and 'Not Found' not in probe.stderr:
            raise RuntimeError(probe.stderr.strip())
        subprocess.run([
            'gh', 'release', 'create', tag,
            '--repo', fork,
            '--title', target,
            '--notes', f'Replay evidence for {upstream}#{issue_num}.',
        ], check=True)
        remote = json.loads(subprocess.check_output(['gh', 'api', route], text=True))
    else:
        remote = json.loads(probe.stdout)

    assets = {a['name']: a for a in remote.get('assets', [])}
    missing = [str(p) for p in files if p.name not in assets]
    if missing:
        subprocess.run(['gh', 'release', 'upload', tag, '--repo', fork, *missing], check=True)
        remote = json.loads(subprocess.check_output(['gh', 'api', route], text=True))
        assets = {a['name']: a for a in remote.get('assets', [])}

    links = []
    for p in files:
        asset = assets[p.name]
        expected_digest = 'sha256:' + tasks.digest(p)
        if asset.get('state') != 'uploaded':
            raise RuntimeError(f'Asset not uploaded cleanly: {p.name}')
        if asset.get('digest') and asset['digest'] != expected_digest:
            raise RuntimeError(f'Published digest mismatch for {p.name}: {asset.get("digest")} != {expected_digest}')
        links.append((p.name, asset['browser_download_url'], tasks.digest(p)))
    return tag, links


def phase_publish(out_summary: Path, fork: str):
    built_manifest = json.loads((out_summary / 'build_manifest.json').read_text(encoding='utf-8'))
    rows = {r['module']: r for r in tasks.module_rows()}
    results = []

    for entry in built_manifest:
        target = entry['target']
        issue_num = entry['issue']
        if entry['exit_code'] != 0:
            results.append(entry)
            continue

        out_dir = Path(entry['out_dir'])
        targets = tasks.select(rows.values(), target)
        verified = evidence.verify(out_dir, targets, rows)
        receipt = entry['receipt']
        kernel_check_seconds = entry.get('kernel_check_seconds')

        files = [out_dir / 'receipt.json', out_dir / 'build.log', out_dir / 'targets.tar.gz']
        if (out_dir / evidence.REPLAY_FILE).is_file():
            files.append(out_dir / evidence.REPLAY_FILE)

        tag, asset_links = publish_release(fork, tasks.repo, target, issue_num, files)
        links_md = ' · '.join(f'[{name}]({url})' for name, url, _ in asset_links)
        sha_lines = [f'{sha}  {name}' for name, _, sha in asset_links]
        for tid, osha in sorted(receipt['objects'].items()):
            sha_lines.append(f'{osha}  {tid} (.olean)')

        rebuilt_count = len(verified['rebuilt_project_modules'])
        extra_kernel_note = (
            f' Target-level `lake env leanchecker --verbose` also passed in {kernel_check_seconds} s.'
            if kernel_check_seconds is not None else ''
        )

        comment_body = (
            f"Replay submission\n\n"
            f"{target}, Lake exit 0 on {verified['identity']['platform']}. "
            f"Of {len(verified['tasks'])} requested targets, Lake built {len(verified['built_targets'])} "
            f"and the kernel replayed {len(verified['kernel_replayed_targets'])} from cache "
            f"({rebuilt_count} prerequisite project imports built locally). "
            f"Elapsed Lake time {receipt['elapsed_seconds']} s.{extra_kernel_note}\n\n"
            f"{links_md}\n\n"
            f"Bundle SHA-256 `{receipt['bundle_sha256']}`.\n\n"
            f"```text\n" + '\n'.join(sha_lines) + "\n```\n"
        )

        md_file = out_summary / f'submission-{target}-{issue_num}.md'
        md_file.write_text(comment_body, encoding='utf-8')

        results.append({
            'target': target,
            'issue': issue_num,
            'exit_code': 0,
            'release_tag': tag,
            'elapsed_seconds': receipt['elapsed_seconds'],
            'rebuilt_project_modules_count': rebuilt_count,
            'bundle_sha256': receipt['bundle_sha256'],
            'comment_file': md_file.name,
            'comment_body': comment_body,
        })
        print(f'Published release {tag} for {target}', flush=True)

    (out_summary / 'results.json').write_text(json.dumps(results, indent=2) + '\n', encoding='utf-8')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--phase', choices=('build', 'publish'), required=True)
    args = parser.parse_args()

    out_summary = Path(os.environ['RUNNER_TEMP']) / 'replay-submissions'
    if args.phase == 'build':
        work_dir = Path(os.environ['WORK_DIR']).resolve()
        pairs = parse_pairs(os.environ['INPUT_ASSIGNMENTS'])
        phase_build(work_dir, out_summary, pairs)
    else:
        phase_publish(out_summary, os.environ['FORK_REPO'])


if __name__ == '__main__':
    main()
