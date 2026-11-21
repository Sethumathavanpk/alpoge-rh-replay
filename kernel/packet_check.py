#!/usr/bin/env python3
"""Compile a replay packet, export its declaration cone, and check it with nanoda.

Extends kernel/independent-check.sh from the 2-declaration Mathlib statement
cone (Pilot.lean) to an entire project packet from tracker/modules.jsonl.gz,
without modifying the prepared replay volume:

  1. verifies Lean 4.33.1, Mathlib 0df444a3..., and every packet module's
     source_sha256 against tracker/modules.jsonl.gz;
  2. compiles all modules in the packet (in dependency order) into an external
     output directory using the project's lakefile.toml Lean options;
  3. imports the packet modules into a synthetic root module, inspects
     env.header.moduleData to collect every non-internal and user-private
     declaration defined by the packet's modules, and exports their full
     declaration-level dependency cone with lean4export (NDJSON 3.1.0);
  4. strictly counts every declaration record in the export (failing on any
     unrecognized record shape) and type-checks the export with nanoda_lib in
     strict mode (unpermitted_axiom_hard_error: true).

Usage:
  python3 kernel/packet_check.py <prepared-volume-dir> <packet-or-module-id> [output-dir] [--jobs N]
"""
from __future__ import annotations

import argparse
from collections import deque
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

LEAN_VERSION = "4.33.1"
LEAN_COMMIT = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
MATHLIB_COMMIT = "0df444a360eaa60ab8c11dca51a86af692955474"

LEAN4EXPORT_REPO = "https://github.com/leanprover/lean4export.git"
LEAN4EXPORT_COMMIT = "15f6055e299ad5b89345e533cc2192f4cc00f659"  # tag v4.33.0
NANODA_REPO = "https://github.com/ammkrn/nanoda_lib.git"
NANODA_COMMIT = "0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929"  # v0.4.32

PERMITTED_AXIOMS = [
    "propext",
    "Classical.choice",
    "Quot.sound",
    "Lean.trustCompiler",
]
DECL_KINDS = frozenset({"axiom", "def", "thm", "opaque", "quot", "inductive"})

# Matches lakefile.toml in the published archive.
BASE_LEAN_FLAGS = [
    "--tstack=400000",
    "-DautoImplicit=false",
    "-DrelaxedAutoImplicit=false",
    "-DmaxSynthPendingDepth=3",
    "-Dpp.unicode.fun=true",
    "-DmaxHeartbeats=4000000",
]
FIELDS_PREFIXES = ("GroundTheory.LocalFields.", "GroundTheory.GlobalFields.")


class CheckFailure(RuntimeError):
    """Raised when any integrity, build, export, or kernel check fails."""


def fail(msg: str) -> "NoReturn":  # type: ignore[name-defined]
    print(f"PACKET_INDEPENDENT_KERNEL_FAILED: {msg}", file=sys.stderr)
    raise SystemExit(1)


def exe_name(stem: str) -> str:
    return f"{stem}.exe" if os.name == "nt" else stem


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def lean_flags_for_module(module: str, jobs: int) -> list[str]:
    flags = ["-j", str(jobs), *BASE_LEAN_FLAGS]
    if module.startswith(FIELDS_PREFIXES):
        flags.append("-DsynthInstance.maxHeartbeats=400000")
    return flags


def _win_peak_rss_kb(proc: subprocess.Popen) -> int:
    import ctypes
    import ctypes.wintypes

    class PROCESS_MEMORY_COUNTERS(ctypes.Structure):
        _fields_ = [
            ("cb", ctypes.wintypes.DWORD),
            ("PageFaultCount", ctypes.wintypes.DWORD),
            ("PeakWorkingSetSize", ctypes.c_size_t),
            ("WorkingSetSize", ctypes.c_size_t),
            ("QuotaPeakPagedPoolUsage", ctypes.c_size_t),
            ("QuotaPagedPoolUsage", ctypes.c_size_t),
            ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t),
            ("QuotaNonPagedPoolUsage", ctypes.c_size_t),
            ("PagefileUsage", ctypes.c_size_t),
            ("PeakPagefileUsage", ctypes.c_size_t),
        ]

    pmc = PROCESS_MEMORY_COUNTERS()
    pmc.cb = ctypes.sizeof(pmc)
    ok = ctypes.windll.kernel32.K32GetProcessMemoryInfo(
        ctypes.wintypes.HANDLE(int(proc._handle)),  # type: ignore[attr-defined]
        ctypes.byref(pmc),
        pmc.cb,
    )
    return int(pmc.PeakWorkingSetSize // 1024) if ok else 0


def run_timed(
    cmd: list[str],
    *,
    env: dict[str, str] | None = None,
    cwd: Path | None = None,
    stdout_path: Path | None = None,
    stderr_path: Path | None = None,
) -> tuple[int, float, int]:
    """Run cmd, returning (exit_code, wall_seconds, peak_rss_kb)."""
    full_cmd = ["nice", "-n", "10", *cmd] if os.name != "nt" and shutil.which("nice") else list(cmd)
    out_f = stdout_path.open("wb") if stdout_path else subprocess.DEVNULL
    err_f = (
        stderr_path.open("wb")
        if stderr_path
        else (subprocess.STDOUT if stdout_path else subprocess.DEVNULL)
    )
    try:
        ru_before = 0
        if os.name != "nt":
            import resource

            ru_before = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
        t0 = time.monotonic()
        proc = subprocess.Popen(full_cmd, env=env, cwd=cwd, stdout=out_f, stderr=err_f)
        rc = proc.wait()
        wall = time.monotonic() - t0
        if os.name == "nt":
            rss_kb = _win_peak_rss_kb(proc)
        else:
            import resource

            ru_after = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
            raw = max(ru_before, ru_after)
            # macOS reports ru_maxrss in bytes; Linux reports KiB.
            rss_kb = int(raw // 1024) if sys.platform == "darwin" else int(raw)
        return rc, wall, rss_kb
    finally:
        if stdout_path and hasattr(out_f, "close"):
            out_f.close()  # type: ignore[union-attr]
        if stderr_path and hasattr(err_f, "close"):
            err_f.close()  # type: ignore[union-attr]


def select_and_order_modules(rows: list[dict], target: str) -> list[dict]:
    """Select modules matching a packet ID or module ID and order intra-set imports first."""
    selected = [r for r in rows if target in (r["packet"], r["id"], r["module"])]
    if not selected:
        raise CheckFailure(f"unknown packet or module target: {target}")
    by_id = {r["id"]: r for r in selected}
    indegree = {r["id"]: 0 for r in selected}
    dependents: dict[str, list[str]] = {r["id"]: [] for r in selected}
    for r in selected:
        for imp in set(r["imports"]):
            if imp in by_id:
                indegree[r["id"]] += 1
                dependents[imp].append(r["id"])
    ready = deque(
        sorted(
            (mid for mid, deg in indegree.items() if deg == 0),
            key=lambda mid: (by_id[mid]["depth"], mid),
        )
    )
    ordered: list[dict] = []
    while ready:
        mid = ready.popleft()
        ordered.append(by_id[mid])
        for dep in sorted(dependents[mid]):
            indegree[dep] -= 1
            if indegree[dep] == 0:
                ready.append(dep)
    if len(ordered) != len(selected):
        raise CheckFailure(f"dependency cycle inside target {target}")
    return ordered


def count_export_records(ndjson_path: Path) -> dict:
    """Strictly count declaration records in an NDJSON export and extract metadata/axioms.

    Matches kernel/independent-check.sh: fails loudly on any single-key object
    other than 'meta' or the six known declaration kinds, or any multi-key
    object carrying a declaration kind key.
    """
    counts = {k: 0 for k in DECL_KINDS}
    names: dict[int, str] = {0: ""}
    axiom_names: list[str] = []
    meta: dict | None = None
    line_count = 0

    with ndjson_path.open("r", encoding="utf-8") as f:
        for line_no, line in enumerate(f, 1):
            stripped = line.strip()
            if not stripped:
                continue
            line_count += 1
            try:
                obj = json.loads(stripped)
            except Exception as exc:
                raise CheckFailure(f"invalid JSON on line {line_no} of {ndjson_path}: {exc}") from exc
            if not isinstance(obj, dict):
                raise CheckFailure(f"non-object JSON record on line {line_no} of {ndjson_path}")

            if "in" in obj:
                idx = obj["in"]
                if "str" in obj and isinstance(obj["str"], dict):
                    pre = names.get(obj["str"].get("pre", 0), "")
                    seg = obj["str"].get("str", "")
                    names[idx] = f"{pre}.{seg}" if pre else seg
                elif "num" in obj and isinstance(obj["num"], dict):
                    pre = names.get(obj["num"].get("pre", 0), "")
                    seg = str(obj["num"].get("i", 0))
                    names[idx] = f"{pre}.{seg}" if pre else seg

            kinds = DECL_KINDS.intersection(obj)
            if len(obj) == 1 and kinds:
                kind = next(iter(kinds))
                counts[kind] += 1
                if kind == "axiom" and isinstance(obj["axiom"], dict):
                    ax_idx = obj["axiom"].get("name")
                    axiom_names.append(names.get(ax_idx, f"<name#{ax_idx}>"))
            elif len(obj) == 1 and "meta" in obj:
                meta = obj["meta"]
            elif kinds or len(obj) == 1:
                raise CheckFailure(f"unrecognized record shape in export: {sorted(obj)[:4]}")

    if meta is None:
        raise CheckFailure(f"missing meta record in export {ndjson_path}")
    return {
        "meta": meta,
        "counts": counts,
        "total_declarations": sum(counts.values()),
        "axioms": axiom_names,
        "lines": line_count,
    }


def make_nanoda_config(export_path: Path, jobs: int) -> dict:
    return {
        "export_file_path": str(export_path),
        "use_stdin": False,
        "num_threads": jobs,
        "stack_size_bytes": 1073741824,
        "permitted_axioms": list(PERMITTED_AXIOMS),
        "unpermitted_axiom_hard_error": True,
        "nat_extension": True,
        "string_extension": True,
        "print_success_message": True,
    }


def ensure_lean4export(out_dir: Path, tc_bin: Path, env: dict[str, str]) -> Path:
    override = os.environ.get("LEAN4EXPORT_BIN")
    if override:
        p = Path(override).resolve()
        if not p.is_file():
            raise CheckFailure(f"LEAN4EXPORT_BIN does not exist: {p}")
        return p
    l4e_dir = out_dir / "tools" / "lean4export"
    l4e_bin = l4e_dir / ".lake" / "build" / "bin" / exe_name("lean4export")
    if l4e_bin.is_file() and (l4e_dir / ".git").is_dir():
        head = subprocess.check_output(["git", "-C", str(l4e_dir), "rev-parse", "HEAD"], text=True).strip()
        if head != LEAN4EXPORT_COMMIT:
            raise CheckFailure(f"lean4export checkout at {head}, expected {LEAN4EXPORT_COMMIT}")
        return l4e_bin
    print(f"== building lean4export @ {LEAN4EXPORT_COMMIT} (with Lean {LEAN_VERSION})", flush=True)
    l4e_dir.parent.mkdir(parents=True, exist_ok=True)
    if not (l4e_dir / ".git").is_dir():
        subprocess.run(["git", "clone", "--quiet", LEAN4EXPORT_REPO, str(l4e_dir)], check=True)
    subprocess.run(["git", "-C", str(l4e_dir), "checkout", "--quiet", LEAN4EXPORT_COMMIT], check=True)
    head = subprocess.check_output(["git", "-C", str(l4e_dir), "rev-parse", "HEAD"], text=True).strip()
    if head != LEAN4EXPORT_COMMIT:
        raise CheckFailure(f"lean4export checkout at {head}, expected {LEAN4EXPORT_COMMIT}")
    log = out_dir / "lean4export-build.log"
    rc, _, _ = run_timed([str(tc_bin / exe_name("lake")), "build"], env=env, cwd=l4e_dir, stdout_path=log)
    if rc != 0 or not l4e_bin.is_file():
        raise CheckFailure(f"building lean4export failed (see {log})")
    return l4e_bin


def ensure_lean4export_file_helper(out_dir: Path, tc_bin: Path, env: dict[str, str]) -> Path:
    """Build a tiny native wrapper linking pinned Export.olean when argv exceeds OS limits."""
    ensure_lean4export(out_dir, tc_bin, env)
    l4e_dir = out_dir / "tools" / "lean4export"
    helper_dir = out_dir / "tools" / "lean4export-file"
    helper_bin = helper_dir / ".lake" / "build" / "bin" / exe_name("lean4export_file")
    if helper_bin.is_file():
        return helper_bin
    helper_dir.mkdir(parents=True, exist_ok=True)
    (helper_dir / "lean-toolchain").write_text(
        (l4e_dir / "lean-toolchain").read_text(encoding="utf-8"), encoding="utf-8", newline="\n"
    )
    (helper_dir / "lakefile.toml").write_text(
        'name = "lean4export_file"\n'
        'defaultTargets = ["lean4export_file"]\n\n'
        "[[require]]\n"
        'name = "lean4export"\n'
        'path = "../lean4export"\n\n'
        "[[lean_exe]]\n"
        'name = "lean4export_file"\n'
        'root = "MainFile"\n'
        "supportInterpreter = true\n",
        encoding="utf-8",
        newline="\n",
    )
    (helper_dir / "MainFile.lean").write_text(
        "import Export\n"
        "open Lean\n\n"
        "def main (args : List String) : IO Unit := do\n"
        "  initSearchPath (← findSysroot)\n"
        '  let (opts, posArgs) := args.partition (fun s => s.startsWith "--" && s.length ≥ 3)\n'
        "  let [modName, constFile] := posArgs\n"
        '    | throw <| IO.userError "usage: lean4export_file [--opts...] <module> <constants-file>"\n'
        "  let raw ← IO.FS.readFile constFile\n"
        '  let cs := (raw.splitOn "\\n").foldr (fun line acc =>\n'
        "    let s := line.dropRightWhile (· == '\\r')\n"
        "    if s.isEmpty then acc else s :: acc) []\n"
        '  let imports := #[{ module := Syntax.decodeNameLit ("`" ++ modName) |>.get! }]\n'
        "  let env ← importModules imports {}\n"
        '  let constants := cs.map fun c => Syntax.decodeNameLit ("`" ++ c) |>.get!\n'
        "  M.run env do\n"
        "    let _ ← initState env opts\n"
        "    dumpMetadata\n"
        "    for c in constants do\n"
        "      modify (fun st => { st with noMDataExprs := {} })\n"
        "      dumpConstant c\n",
        encoding="utf-8",
        newline="\n",
    )
    log = out_dir / "lean4export-file-build.log"
    rc, _, _ = run_timed([str(tc_bin / exe_name("lake")), "build"], env=env, cwd=helper_dir, stdout_path=log)
    if rc != 0 or not helper_bin.is_file():
        raise CheckFailure(f"building lean4export_file wrapper failed (see {log})")
    return helper_bin


def ensure_nanoda(out_dir: Path, jobs: int) -> Path:
    override = os.environ.get("NANODA_BIN")
    if override:
        p = Path(override).resolve()
        if not p.is_file():
            raise CheckFailure(f"NANODA_BIN does not exist: {p}")
        return p
    nan_dir = out_dir / "tools" / "nanoda_lib"
    nan_bin = nan_dir / "target" / "release" / exe_name("nanoda_bin")
    if nan_bin.is_file() and (nan_dir / ".git").is_dir():
        head = subprocess.check_output(["git", "-C", str(nan_dir), "rev-parse", "HEAD"], text=True).strip()
        if head != NANODA_COMMIT:
            raise CheckFailure(f"nanoda_lib checkout at {head}, expected {NANODA_COMMIT}")
        return nan_bin
    cargo = shutil.which("cargo")
    if not cargo:
        cargo_home = os.environ.get("CARGO_HOME")
        if cargo_home and (Path(cargo_home) / "bin" / exe_name("cargo")).is_file():
            cargo = str(Path(cargo_home) / "bin" / exe_name("cargo"))
    if not cargo:
        raise CheckFailure("cargo not found; install a Rust toolchain (rustup) or set NANODA_BIN")
    if subprocess.run([cargo, "--version"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode != 0:
        raise CheckFailure("cargo is present but not runnable; configure a default rustup toolchain")
    print(f"== building nanoda_lib @ {NANODA_COMMIT}", flush=True)
    nan_dir.parent.mkdir(parents=True, exist_ok=True)
    if not (nan_dir / ".git").is_dir():
        subprocess.run(["git", "clone", "--quiet", NANODA_REPO, str(nan_dir)], check=True)
    subprocess.run(["git", "-C", str(nan_dir), "checkout", "--quiet", NANODA_COMMIT], check=True)
    head = subprocess.check_output(["git", "-C", str(nan_dir), "rev-parse", "HEAD"], text=True).strip()
    if head != NANODA_COMMIT:
        raise CheckFailure(f"nanoda_lib checkout at {head}, expected {NANODA_COMMIT}")
    log = out_dir / "nanoda-build.log"
    rc, _, _ = run_timed([cargo, "build", "--release", "--locked", "-j", str(jobs)], cwd=nan_dir, stdout_path=log)
    if rc != 0 or not nan_bin.is_file():
        raise CheckFailure(f"building nanoda_lib failed (see {log})")
    return nan_bin


def argv_fits_os_limit(cmd: list[str]) -> bool:
    total_chars = sum(len(a) + 1 for a in cmd)
    if os.name == "nt":
        # Windows CreateProcessW caps lpCommandLine at 32,767 UTF-16 code units.
        return total_chars < 30_000
    try:
        arg_max = int(os.sysconf("SC_ARG_MAX"))
    except (AttributeError, ValueError, OSError):
        arg_max = 262_144
    return total_chars < min(arg_max // 2, 1_000_000)


def collect_declarations_lean_source(target_modules: list[str], decls_out: Path, stats_out: Path, root_mod: str) -> str:
    mods_lit = ", ".join(f"`{m}" for m in target_modules)
    decls_str = json.dumps(str(decls_out))
    stats_str = json.dumps(str(stats_out))
    return f"""import {root_mod}
import Lean

open Lean in
#eval show MetaM Unit from do
  let env ← getEnv
  let targetSet : NameSet := [{mods_lit}].foldl NameSet.insert {{}}
  let mut rootDecls : Array String := #[]
  let mut publicCount : Nat := 0
  let mut privateCount : Nat := 0
  let mut internalAuxCount : Nat := 0
  let mut unsafeCount : Nat := 0
  let mut thmCount : Nat := 0
  let mut defCount : Nat := 0
  let mut inductCount : Nat := 0
  let mut ctorCount : Nat := 0
  let mut recCount : Nat := 0
  let mut opaqueCount : Nat := 0
  let mut axiomCount : Nat := 0
  let mut quotCount : Nat := 0
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if targetSet.contains m then
      let md := env.header.moduleData[i]!
      for j in [0:md.constNames.size] do
        let c := md.constNames[j]!
        let cinfo := md.constants[j]!
        if cinfo.isUnsafe then
          unsafeCount := unsafeCount + 1
        else
          match cinfo with
          | .thmInfo _ => thmCount := thmCount + 1
          | .defnInfo _ => defCount := defCount + 1
          | .inductInfo _ => inductCount := inductCount + 1
          | .ctorInfo _ => ctorCount := ctorCount + 1
          | .recInfo _ => recCount := recCount + 1
          | .opaqueInfo _ => opaqueCount := opaqueCount + 1
          | .axiomInfo _ => axiomCount := axiomCount + 1
          | .quotInfo _ => quotCount := quotCount + 1
          let isUserPriv := match privateToUserName? c with
            | some u => !u.isInternal
            | none => false
          if !c.isInternal || isUserPriv then
            let s := c.toString
            if Syntax.decodeNameLit ("`" ++ s) != some c then
              throwError "Constant {{s}} in {{m}} cannot be round-tripped via Syntax.decodeNameLit"
            rootDecls := rootDecls.push s
            if isUserPriv then
              privateCount := privateCount + 1
            else
              publicCount := publicCount + 1
          else
            internalAuxCount := internalAuxCount + 1
  IO.FS.writeFile {decls_str} (String.intercalate "\\n" rootDecls.toList ++ "\\n")
  let statsJson := Json.mkObj [
    ("root_declarations", rootDecls.size),
    ("public_non_internal", publicCount),
    ("user_private", privateCount),
    ("internal_auxiliaries", internalAuxCount),
    ("unsafe_skipped", unsafeCount),
    ("module_constants_by_kind", Json.mkObj [
      ("thm", thmCount),
      ("def", defCount),
      ("inductive", inductCount),
      ("ctor", ctorCount),
      ("rec", recCount),
      ("opaque", opaqueCount),
      ("axiom", axiomCount),
      ("quot", quotCount)
    ])
  ]
  IO.FS.writeFile {stats_str} (statsJson.pretty ++ "\\n")
"""


def run_packet_check(vol_dir: Path, target: str, out_dir: Path, jobs: int) -> int:
    repo_root = Path(__file__).resolve().parent.parent
    tracker_dir = repo_root / "tracker"
    vol_dir = vol_dir.resolve()
    out_dir = out_dir.resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    # ---- Verify pinned Lean toolchain and Mathlib ---------------------------
    tc_dir = vol_dir / "elan" / "toolchains" / f"leanprover--lean4---v{LEAN_VERSION}"
    tc_bin = tc_dir / "bin"
    lean_bin = tc_bin / exe_name("lean")
    if not lean_bin.is_file():
        raise CheckFailure(f"no leanprover--lean4---v{LEAN_VERSION} toolchain at {tc_dir}")

    base_env = os.environ.copy()
    base_env["ELAN_HOME"] = str(vol_dir / "elan")
    base_env["LEAN_NUM_THREADS"] = str(jobs)
    base_env["PATH"] = str(tc_bin) + os.pathsep + base_env.get("PATH", "")

    lean_ver = subprocess.check_output([str(lean_bin), "--version"], env=base_env, text=True).strip()
    if LEAN_VERSION not in lean_ver or LEAN_COMMIT not in lean_ver:
        raise CheckFailure(f"unexpected Lean version output: {lean_ver}")

    mathlib_git = vol_dir / "lean" / ".lake" / "packages" / "mathlib"
    if not (mathlib_git / ".git").is_dir():
        raise CheckFailure(f"missing mathlib package checkout at {mathlib_git}")
    mathlib_head = subprocess.check_output(["git", "-C", str(mathlib_git), "rev-parse", "HEAD"], text=True).strip()
    summary_mathlib = json.loads((tracker_dir / "summary.json").read_text(encoding="utf-8"))["mathlib_commit"]
    if mathlib_head != MATHLIB_COMMIT or mathlib_head != summary_mathlib:
        raise CheckFailure(f"mathlib commit {mathlib_head} does not match pinned {MATHLIB_COMMIT}")

    # ---- Load ledger & verify source_sha256 for every module ----------------
    with gzip.open(tracker_dir / "modules.jsonl.gz", "rt", encoding="utf-8") as f:
        all_rows = [json.loads(line) for line in f if line.strip()]
    by_id = {r["id"]: r for r in all_rows}
    targets = select_and_order_modules(all_rows, target)
    target_ids = {r["id"] for r in targets}

    pkt_dir = out_dir / target
    src_dir = pkt_dir / "src"
    lib_dir = pkt_dir / "lib"
    if pkt_dir.exists():
        shutil.rmtree(pkt_dir)
    src_dir.mkdir(parents=True)
    lib_dir.mkdir(parents=True)

    # Package olean directories from the prepared volume (read-only).
    pkg_olean_dirs: list[str] = []
    pkgs_root = vol_dir / "lean" / ".lake" / "packages"
    if pkgs_root.is_dir():
        for pkg in sorted(pkgs_root.iterdir()):
            d = pkg / ".lake" / "build" / "lib" / "lean"
            if d.is_dir():
                pkg_olean_dirs.append(str(d))
    if not pkg_olean_dirs:
        raise CheckFailure(f"no package olean dirs found under {pkgs_root}")

    # Check external project imports (for depth > 0 packets).
    ext_search_dirs: list[Path] = []
    if (out_dir / "lib").is_dir():
        ext_search_dirs.append(out_dir / "lib")
    vol_proj_lib = vol_dir / "lean" / ".lake" / "build" / "lib" / "lean"
    if vol_proj_lib.is_dir():
        ext_search_dirs.append(vol_proj_lib)

    needed_ext_dirs: list[str] = []
    for r in targets:
        for imp_id in r["imports"]:
            if imp_id in target_ids:
                continue
            imp_mod = by_id[imp_id]["module"]
            rel_olean = Path(*imp_mod.split(".")).with_suffix(".olean")
            found = next((d for d in ext_search_dirs if (d / rel_olean).is_file()), None)
            if found is None:
                raise CheckFailure(
                    f"{r['id']} ({r['module']}) requires external project import {imp_id} ({imp_mod}), "
                    f"whose .olean is not built in {ext_search_dirs or [vol_proj_lib]}"
                )
            if str(found) not in needed_ext_dirs:
                needed_ext_dirs.append(str(found))

    for r in targets:
        rel_lean = Path(*r["module"].split(".")).with_suffix(".lean")
        vol_src = vol_dir / "lean" / "src" / rel_lean
        if not vol_src.is_file():
            raise CheckFailure(f"missing source file in volume: {vol_src}")
        actual_sha = sha256_file(vol_src)
        if actual_sha != r["source_sha256"]:
            raise CheckFailure(
                f"source_sha256 mismatch for {r['id']} ({r['module']}): {actual_sha} != {r['source_sha256']}"
            )
        dst_src = src_dir / rel_lean
        dst_src.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(vol_src, dst_src)
    print(f"SOURCE_HASHES_VERIFIED target={target} modules={len(targets)}", flush=True)

    # ---- Step 0: Build or locate pinned tools -------------------------------
    l4e_bin = ensure_lean4export(out_dir, tc_bin, base_env)
    nanoda_bin = ensure_nanoda(out_dir, jobs)
    print(f"lean4export: {l4e_bin}", flush=True)
    print(f"nanoda:      {nanoda_bin}", flush=True)

    lean_env = base_env.copy()
    lean_env["LEAN_PATH"] = os.pathsep.join([*pkg_olean_dirs, *needed_ext_dirs, str(lib_dir)])

    # ---- Step 1: Compile packet modules + synthetic root + collect decls ----
    print(f"== compiling {len(targets)} module(s) for {target} (jobs={jobs})", flush=True)
    compile_logs = pkt_dir / "compile-logs"
    compile_logs.mkdir(parents=True, exist_ok=True)
    compile_t0 = time.monotonic()
    compile_peak_kb = 0
    per_module_stats: list[dict] = []

    for idx, r in enumerate(targets, 1):
        mod = r["module"]
        rel = Path(*mod.split("."))
        src_file = src_dir / rel.with_suffix(".lean")
        olean_file = lib_dir / rel.with_suffix(".olean")
        olean_file.parent.mkdir(parents=True, exist_ok=True)
        log_file = compile_logs / f"{r['id']}.log"
        cmd = [str(lean_bin), *lean_flags_for_module(mod, jobs), "-R", str(src_dir), str(src_file), "-o", str(olean_file)]
        rc, wall, rss_kb = run_timed(cmd, env=lean_env, stdout_path=log_file)
        compile_peak_kb = max(compile_peak_kb, rss_kb)
        if rc != 0 or not olean_file.is_file():
            raise CheckFailure(f"compiling {r['id']} ({mod}) failed with exit {rc} (see {log_file})")
        olean_sha = sha256_file(olean_file)
        per_module_stats.append(
            {
                "id": r["id"],
                "module": mod,
                "wall_seconds": round(wall, 2),
                "maxrss_kb": rss_kb,
                "olean_sha256": olean_sha,
            }
        )
        print(
            f"  [{idx:2d}/{len(targets)}] {r['id']} {mod} ({wall:.1f}s, peak_rss={rss_kb / 1048576:.2f} GB)",
            flush=True,
        )

    safe_tag = "".join(ch if ch.isalnum() else "_" for ch in target)
    root_mod = f"PacketRoot_{safe_tag}"
    root_lean = pkt_dir / f"{root_mod}.lean"
    root_olean = lib_dir / f"{root_mod}.olean"
    root_lean.write_text(
        "".join(f"import {r['module']}\n" for r in targets),
        encoding="utf-8",
        newline="\n",
    )
    rc, root_wall, root_rss = run_timed(
        [str(lean_bin), "-j", str(jobs), "-R", str(pkt_dir), str(root_lean), "-o", str(root_olean)],
        env=lean_env,
        cwd=pkt_dir,
        stdout_path=pkt_dir / "root-compile.log",
    )
    compile_peak_kb = max(compile_peak_kb, root_rss)
    if rc != 0 or not root_olean.is_file():
        raise CheckFailure(f"compiling {root_mod}.lean failed (see {pkt_dir / 'root-compile.log'})")
    compile_wall = time.monotonic() - compile_t0

    decls_file = pkt_dir / "declarations.txt"
    decl_stats_file = pkt_dir / "packet-decl-stats.json"
    collector_lean = pkt_dir / "CollectDecls.lean"
    collector_lean.write_text(
        collect_declarations_lean_source([r["module"] for r in targets], decls_file, decl_stats_file, root_mod),
        encoding="utf-8",
        newline="\n",
    )
    rc, collect_wall, collect_rss = run_timed(
        [str(lean_bin), "-j", str(jobs), "-R", str(pkt_dir), str(collector_lean)],
        env=lean_env,
        cwd=pkt_dir,
        stdout_path=pkt_dir / "collect-decls.log",
    )
    compile_peak_kb = max(compile_peak_kb, collect_rss)
    if rc != 0 or not decls_file.is_file() or not decl_stats_file.is_file():
        raise CheckFailure(f"declaration collection failed (see {pkt_dir / 'collect-decls.log'})")

    root_decls = [line.strip() for line in decls_file.read_text(encoding="utf-8").splitlines() if line.strip()]
    pkt_decl_stats = json.loads(decl_stats_file.read_text(encoding="utf-8"))
    print(
        f"PACKET_COMPILE_PASSED target={target} modules={len(targets)} "
        f"wall_seconds={compile_wall:.1f} maxrss_kb={compile_peak_kb} "
        f"root_declarations={len(root_decls)}",
        flush=True,
    )

    # ---- Step 2: Export the packet cone with lean4export --------------------
    ndjson_path = pkt_dir / f"{target}.ndjson"
    export_log = pkt_dir / "export.log"
    direct_cmd = [str(l4e_bin), root_mod, "--", *root_decls]
    if argv_fits_os_limit(direct_cmd):
        export_cmd = direct_cmd
        export_mode = "direct-cli"
    else:
        helper_bin = ensure_lean4export_file_helper(out_dir, tc_bin, base_env)
        export_cmd = [str(helper_bin), root_mod, str(decls_file)]
        export_mode = "file-wrapper"

    print(
        f"== exporting {len(root_decls)} root declaration(s) from {target} with lean4export ({export_mode})",
        flush=True,
    )
    rc, export_wall, export_rss_kb = run_timed(
        export_cmd,
        env=lean_env,
        stdout_path=ndjson_path,
        stderr_path=export_log,
    )
    if rc != 0:
        raise CheckFailure(f"lean4export failed with exit {rc} (see {export_log})")

    export_bytes = ndjson_path.stat().st_size
    export_sha256 = sha256_file(ndjson_path)
    export_info = count_export_records(ndjson_path)
    counts = export_info["counts"]
    breakdown = " ".join(f"{k}={counts[k]}" for k in sorted(counts))
    print(f"  breakdown: {breakdown}", flush=True)
    print(f"  axioms in cone: {export_info['axioms']}", flush=True)
    print(
        f"EXPORT_DONE bytes={export_bytes} declarations={export_info['total_declarations']} "
        f"wall_seconds={export_wall:.1f} maxrss_kb={export_rss_kb} sha256={export_sha256}",
        flush=True,
    )

    # ---- Step 3: Check with nanoda in strict mode ---------------------------
    cfg_path = pkt_dir / "nanoda-config.json"
    cfg_path.write_text(json.dumps(make_nanoda_config(ndjson_path, jobs), indent=2) + "\n", encoding="utf-8", newline="\n")
    nanoda_log = pkt_dir / "nanoda.log"
    print(f"== checking {ndjson_path.name} with nanoda (strict mode, threads={jobs})", flush=True)
    rc, nanoda_wall, nanoda_rss_kb = run_timed([str(nanoda_bin), str(cfg_path)], stdout_path=nanoda_log)
    nanoda_out = nanoda_log.read_text(encoding="utf-8", errors="replace").strip()
    print(f"wall_seconds={nanoda_wall:.1f} maxrss_kb={nanoda_rss_kb} exit_code={rc}", flush=True)
    if nanoda_out:
        print(nanoda_out, flush=True)

    summary = {
        "target": target,
        "modules": len(targets),
        "jobs": jobs,
        "toolchain": lean_ver,
        "mathlib_commit": mathlib_head,
        "lean4export_commit": LEAN4EXPORT_COMMIT,
        "nanoda_commit": NANODA_COMMIT,
        "export_mode": export_mode,
        "compile": {
            "wall_seconds": round(compile_wall, 1),
            "root_wall_seconds": round(root_wall, 1),
            "collect_wall_seconds": round(collect_wall, 1),
            "maxrss_kb": compile_peak_kb,
            "per_module": per_module_stats,
        },
        "packet_declarations": pkt_decl_stats,
        "export": {
            "wall_seconds": round(export_wall, 1),
            "maxrss_kb": export_rss_kb,
            "bytes": export_bytes,
            "lines": export_info["lines"],
            "sha256": export_sha256,
            "meta": export_info["meta"],
            "declarations_total": export_info["total_declarations"],
            "declarations_by_kind": counts,
            "axioms": export_info["axioms"],
        },
        "nanoda": {
            "wall_seconds": round(nanoda_wall, 1),
            "maxrss_kb": nanoda_rss_kb,
            "exit_code": rc,
            "strict_mode": True,
            "permitted_axioms": PERMITTED_AXIOMS,
            "output": nanoda_out,
        },
    }
    (pkt_dir / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8", newline="\n")

    if rc != 0:
        raise CheckFailure(f"nanoda rejected the export with exit code {rc} (see {nanoda_log})")

    print(
        f"PACKET_INDEPENDENT_KERNEL_PASSED checker=nanoda target={target} modules={len(targets)} "
        f"root_declarations={len(root_decls)} declarations={export_info['total_declarations']} "
        f"export_bytes={export_bytes} export_sha256={export_sha256}",
        flush=True,
    )
    return 0


def build_parser() -> argparse.ArgumentParser:
    script_dir = Path(__file__).resolve().parent
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("volume", type=Path, help="Prepared replay volume directory (contains elan/ and lean/)")
    p.add_argument("target", help="Packet ID (e.g. P0001) or module ID (e.g. M000001)")
    p.add_argument(
        "output",
        type=Path,
        nargs="?",
        default=script_dir / "kernel-out",
        help="External output directory for tools, compiled oleans, and NDJSON export",
    )
    p.add_argument(
        "--jobs",
        type=int,
        default=int(os.environ.get("JOBS", "6")),
        help="Thread cap for Lean, Cargo, and nanoda (default: $JOBS or 6)",
    )
    return p


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.jobs < 1:
        fail("--jobs must be positive")
    try:
        return run_packet_check(args.volume, args.target, args.output, args.jobs)
    except CheckFailure as exc:
        fail(str(exc))


if __name__ == "__main__":
    raise SystemExit(main())
