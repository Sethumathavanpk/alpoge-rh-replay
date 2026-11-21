"""Regenerate the unified diff between published M115085 and compressed CovariantDegrees.lean."""
import argparse
import difflib
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
MODULE = Path("Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CovariantDegrees")
SOURCE = Path("src") / MODULE.with_suffix(".lean")


def load_receipt(here=HERE):
    return json.loads((here / "receipt.json").read_text(encoding="utf-8"))


def checked_bytes(path, expected_sha, label, normalize_crlf=False):
    data = path.read_bytes()
    if normalize_crlf:
        data = data.replace(b"\r\n", b"\n")
    if hashlib.sha256(data).hexdigest() != expected_sha:
        raise SystemExit(f"Unexpected SHA-256 for {label}: {path}")
    return data


def build_diff(published_bytes, revised_bytes, rel_path=SOURCE.as_posix()):
    pub_lines = published_bytes.decode("utf-8").splitlines(keepends=True)
    rev_lines = revised_bytes.decode("utf-8").splitlines(keepends=True)
    diff_lines = difflib.unified_diff(
        pub_lines,
        rev_lines,
        fromfile=f"a/{rel_path}",
        tofile=f"b/{rel_path}",
        lineterm="\n",
    )
    return "".join(diff_lines).encode("utf-8")


def regenerate_diff(project, here=HERE, receipt=None):
    if receipt is None:
        receipt = load_receipt(here)
    published = checked_bytes(project / SOURCE, receipt["sha256"]["published"], "published")
    revised = checked_bytes(here / "CovariantDegrees.lean", receipt["sha256"]["revised"], "revised",
                            normalize_crlf=True)
    diff_bytes = build_diff(published, revised)
    if hashlib.sha256(diff_bytes).hexdigest() != receipt["sha256"]["diff"]:
        raise SystemExit("Unexpected SHA-256 for regenerated diff")
    return published, revised, diff_bytes


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="prepared lean/ directory")
    parser.add_argument("-o", "--output", type=Path, help="write unified diff to file instead of stdout")
    parser.add_argument("--check", action="store_true", help="verify SHA-256 of regenerated diff and exit")
    args = parser.parse_args()
    _, _, diff_bytes = regenerate_diff(args.project.resolve())
    if args.output:
        args.output.write_bytes(diff_bytes)
    elif not args.check:
        sys.stdout.buffer.write(diff_bytes)


if __name__ == "__main__":
    main()
