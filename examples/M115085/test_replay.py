import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE))

import make_diff  # noqa: E402
import replay  # noqa: E402


class M115085ReplayTests(unittest.TestCase):
    def test_receipt_pins_match_tracker_ledger(self):
        receipt = make_diff.load_receipt(HERE)
        summary = json.loads((ROOT / "tracker/summary.json").read_text(encoding="utf-8"))
        self.assertEqual(receipt["task"], "M115085")
        self.assertEqual(receipt["toolchain"], f"leanprover/lean4:v{summary['lean']}")
        self.assertEqual(receipt["mathlib"], summary["mathlib_commit"])

        matched = None
        with gzip.open(ROOT / "tracker/modules.jsonl.gz", "rt", encoding="utf-8") as stream:
            for line in stream:
                if '"M115085"' in line:
                    row = json.loads(line)
                    if row.get("id") == "M115085":
                        matched = row
                        break
        self.assertIsNotNone(matched, "M115085 missing from tracker/modules.jsonl.gz")
        self.assertEqual(matched["module"], ".".join(make_diff.MODULE.parts))
        self.assertEqual(matched["source_sha256"], receipt["sha256"]["published"])

    def test_committed_sources_and_transcript_match_receipt(self):
        receipt = make_diff.load_receipt(HERE)
        for filename, key in (
            ("CovariantDegrees.lean", "revised"),
            ("AuditAll.lean", "audit"),
            ("transcript.txt", "transcript"),
        ):
            raw = (HERE / filename).read_bytes().replace(b"\r\n", b"\n")
            self.assertEqual(hashlib.sha256(raw).hexdigest(), receipt["sha256"][key], filename)

        revised_lines = (HERE / "CovariantDegrees.lean").read_text(encoding="utf-8").splitlines()
        self.assertEqual(len(revised_lines), receipt["comparison"]["source_lines"]["revised"])

        transcript = (HERE / "transcript.txt").read_text(encoding="utf-8")
        self.assertIn(receipt["lean_commit"], transcript)
        self.assertIn(receipt["mathlib"], transcript)
        self.assertIn(receipt["audit"]["metadata"], transcript)
        self.assertIn(receipt["audit"]["axioms_all_public"], transcript)
        self.assertIn(receipt["audit"]["axioms"], transcript)
        self.assertIn("REPLAY_M115085_KERNEL_PASSED", transcript)
        self.assertNotIn("C:\\", transcript)
        self.assertNotIn("/Users/", transcript)

    def test_audit_covers_all_public_declarations(self):
        revised = (HERE / "CovariantDegrees.lean").read_text(encoding="utf-8")
        audit = (HERE / "AuditAll.lean").read_text(encoding="utf-8")
        public_decls = []
        for line in revised.splitlines():
            m = re.match(
                r"^(?:@\[reducible\]\s+)?(?:noncomputable\s+)?(?:def|theorem)\s+([A-Za-z0-9_']+)",
                line,
            )
            if m:
                public_decls.append(m.group(1))
        self.assertEqual(len(public_decls), 25)
        for name in public_decls:
            self.assertRegex(
                audit,
                rf"example\s*:\s*@PublishedCovariantDegrees\.{re.escape(name)}(\.\{{[^}}]+\}})?\s*=\s*"
                rf"@UpperTheory\.Reformulated\.B\.CovariantDegrees\.{re.escape(name)}(\.\{{[^}}]+\}})?\s*:=\s*rfl",
            )
            self.assertIn(
                f"(``PublishedCovariantDegrees.{name}, ``UpperTheory.Reformulated.B.CovariantDegrees.{name})",
                audit,
            )

    def test_make_diff_and_prepare_roundtrip_and_tamper_rejection(self):
        pub = (
            b"import Mathlib\n\n"
            b"theorem UpperTheory.Reformulated.B.CovariantDegrees.demo : True := by\n"
            b"  trivial\n"
        )
        rev = (
            b"import Mathlib.Logic.Basic\n\n"
            b"namespace UpperTheory.Reformulated.B.CovariantDegrees\n"
            b"theorem demo : True := trivial\n"
            b"end UpperTheory.Reformulated.B.CovariantDegrees\n"
        )
        aud = b"import PublishedCovariantDegrees\n"
        expected_ref = (
            b"import Mathlib.Logic.Basic\n\n"
            b"theorem PublishedCovariantDegrees.demo : True := by\n"
            b"  trivial\n"
        )
        diff_bytes = make_diff.build_diff(pub, rev)
        self.assertTrue(diff_bytes.startswith(b"--- a/src/Development/"))
        self.assertNotIn(b"\r", diff_bytes)

        receipt = {
            "sha256": {
                "published": hashlib.sha256(pub).hexdigest(),
                "revised": hashlib.sha256(rev).hexdigest(),
                "reference": hashlib.sha256(expected_ref).hexdigest(),
                "audit": hashlib.sha256(aud).hexdigest(),
                "diff": hashlib.sha256(diff_bytes).hexdigest(),
            }
        }

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            project = root / "project"
            here = root / "here"
            work = root / "work"
            (project / make_diff.SOURCE).parent.mkdir(parents=True)
            (project / make_diff.SOURCE).write_bytes(pub)
            here.mkdir()
            (here / "CovariantDegrees.lean").write_bytes(rev)
            (here / "AuditAll.lean").write_bytes(aud)

            replay.prepare(project, work, here=here, receipt=receipt)
            self.assertEqual((work / make_diff.SOURCE).read_bytes(), rev)
            self.assertEqual((work / "src/PublishedCovariantDegrees.lean").read_bytes(), expected_ref)
            self.assertEqual((work / "src/AuditAll.lean").read_bytes(), aud)

            if shutil.which("git"):
                apply_dir = root / "apply"
                target = apply_dir / make_diff.SOURCE
                target.parent.mkdir(parents=True)
                target.write_bytes(pub)
                patch_file = root / "test.patch"
                patch_file.write_bytes(diff_bytes)
                subprocess.run(
                    ["git", "-c", "core.autocrlf=false", "apply", str(patch_file)],
                    cwd=apply_dir,
                    check=True,
                    env={**os.environ, "GIT_CEILING_DIRECTORIES": str(root)},
                )
                self.assertEqual(target.read_bytes(), rev)

            (project / make_diff.SOURCE).write_bytes(pub + b"\n")
            with self.assertRaisesRegex(SystemExit, "Unexpected SHA-256 for published"):
                replay.prepare(project, root / "work2", here=here, receipt=receipt)


if __name__ == "__main__":
    unittest.main()
