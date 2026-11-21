"""Compare the published and revised M115085 declarations in a pinned Lean environment."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))
from make_diff import MODULE, SOURCE, checked_bytes, load_receipt, regenerate_diff  # noqa: E402

HERE = Path(__file__).resolve().parent
NAMESPACE = b"UpperTheory.Reformulated.B.CovariantDegrees"


def prepare(project, work, here=HERE, receipt=None):
    if receipt is None:
        receipt = load_receipt(here)
    published, revision, _ = regenerate_diff(project, here=here, receipt=receipt)
    audit = checked_bytes(here / "AuditAll.lean", receipt["sha256"]["audit"], "audit", normalize_crlf=True)

    candidate = work / SOURCE
    candidate.parent.mkdir(parents=True, exist_ok=True)
    candidate.write_bytes(revision)

    header, body = published.split(b"\n", 1)
    if header != b"import Mathlib":
        raise SystemExit("Unexpected published import")
    imports = [line for line in revision.splitlines() if line.startswith(b"import ")]
    reference = work / "src/PublishedCovariantDegrees.lean"
    reference_bytes = b"\n".join(imports) + b"\n" + body.replace(NAMESPACE, b"PublishedCovariantDegrees")
    if hashlib.sha256(reference_bytes).hexdigest() != receipt["sha256"]["reference"]:
        raise SystemExit(f"Unexpected SHA-256 for reference: {reference}")
    reference.write_bytes(reference_bytes)

    (work / "src/AuditAll.lean").write_bytes(audit)
    print("Verified the published, revised, reference, audit and regenerated diff digests.", flush=True)


def compile_pair(project, src, receipt=None):
    if receipt is None:
        receipt = load_receipt(HERE)
    pin = receipt["mathlib"]
    manifest = json.loads((project / "lake-manifest.json").read_text(encoding="utf-8"))
    pins = [p.get("rev") for p in manifest["packages"] if p.get("name") == "mathlib"]
    if pins != [pin] or (project / "lean-toolchain").read_text(encoding="utf-8").strip() != receipt["toolchain"]:
        raise SystemExit("Unexpected project toolchain or Mathlib pin")
    mathlib = project / ".lake/packages/mathlib"
    if mathlib.is_dir():
        actual = subprocess.check_output(["git", "-C", str(mathlib), "rev-parse", "HEAD"], text=True).strip()
        if actual != pin:
            raise SystemExit("Unexpected Mathlib checkout")
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    if "version 4.33.1," not in version or receipt["lean_commit"] not in version:
        raise SystemExit(f"Unexpected compiler: {version}")
    print(f"Compiler: {version}", flush=True)
    print(f"Mathlib: {pin}", flush=True)
    search = os.environ.get("LEAN_PATH")
    if not search:
        raise SystemExit("Run the compiler check inside the prepared project's lake env")
    env = {**os.environ, "LEAN_PATH": str(src) + os.pathsep + search}
    lean = ["lean", "--root=.", *receipt["lean_flags"]]
    for name in (Path("PublishedCovariantDegrees"), MODULE, Path("AuditAll")):
        rel = name.with_suffix(".lean").as_posix()
        out = name.with_suffix(".olean").as_posix()
        print(f"Compiling {rel} ...", flush=True)
        subprocess.run([*lean, "-o", out, rel], check=True, env=env, cwd=src)
    print("Running leanchecker on PublishedCovariantDegrees, CovariantDegrees and AuditAll ...", flush=True)
    subprocess.run(["leanchecker", "PublishedCovariantDegrees", ".".join(MODULE.parts), "AuditAll"],
                   check=True, env=env, cwd=src)
    print("REPLAY_M115085_KERNEL_PASSED", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="prepared lean/ directory")
    parser.add_argument("--sources-only", action="store_true", help="verify source and diff digests and exit")
    args = parser.parse_args()
    project = args.project.resolve()
    receipt = load_receipt(HERE)
    with tempfile.TemporaryDirectory(prefix="rh-covariant-") as tmp:
        work = Path(tmp).resolve()
        prepare(project, work, here=HERE, receipt=receipt)
        if not args.sources_only:
            compile_pair(project, work / "src", receipt=receipt)


if __name__ == "__main__":
    main()
