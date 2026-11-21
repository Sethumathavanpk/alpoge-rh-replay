# Independent-kernel pilot

**Status: optional pilot. This is not part of the required replay, and it
does not check the project's full proof of the Riemann Hypothesis.** It
currently covers two self-contained stages with a kernel implementation
(`nanoda_lib`, in Rust) that is independent of Lean's own C++ kernel:

1. **Statement cone (`independent-check.sh`):** the declarations that define
   `RiemannHypothesis` and `riemannZeta` in Mathlib.
2. **Project packet cone (`packet_check.py`):** every declaration in a
   completed 64-module project packet (`P0001`) from `tracker/modules.jsonl.gz`
   together with its transitive Mathlib dependency cone.

## Why

`verify.sh` ends with `leanchecker --fresh Main`. As the README puts it,
"it uses the same Lean kernel implementation": every stage of the required
replay ultimately trusts Lean's C++ kernel, the same kernel that produced
the original claim. An independent kernel checker breaks that circularity
for whatever it is run on. This pilot establishes whether the tooling chain
works at all against this project's pinned environment (Lean 4.33.1,
Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`), and measures what it
costs, starting with the smallest cone that matters: the statement itself.

## What it does

`independent-check.sh <prepared-volume-dir> [output-dir]`:

1. Compiles `kernel/Pilot.lean` against the prepared volume's prebuilt
   Mathlib oleans. `Pilot.lean` imports **only Mathlib** (never the
   project's `Main`) and references `RiemannHypothesis` — the statement
   definition `Audit.lean` anchors on — and `riemannZeta`.
2. Exports the two anchor declarations and their declaration-level
   dependency cone with
   [lean4export](https://github.com/leanprover/lean4export) (NDJSON format).
3. Type-checks the export with
   [nanoda](https://github.com/ammkrn/nanoda_lib) (`nanoda_lib`, a Rust
   implementation of the Lean kernel that shares no code with Lean's C++
   kernel). The checker configuration permits exactly the axioms
   `Audit.lean` permits — `propext`, `Classical.choice`, `Quot.sound` —
   plus `Lean.trustCompiler`, with the Nat and String kernel extensions
   enabled. The checker runs in strict mode
   (`unpermitted_axiom_hard_error: true`): a declaration depending on
   any other axiom is a hard error, not a silent skip.

## Reference run (measured, 2026-11-20)

Machine: home desktop, AMD Ryzen 5 5600 (12 threads), WSL2 Ubuntu 24.04.2,
15 GiB visible RAM. All steps capped at 6 threads, `nice -n 10`; a packet
build was running concurrently on the same machine, so wall times are
shared-load values, not clean benchmarks.

| Step | Wall time | Peak RSS | Result |
| --- | --- | --- | --- |
| Compile `Pilot.lean` (Lean 4.33.1) | 15.4 s | 6.12 GB | `#check` confirms `RiemannHypothesis : Prop`, `riemannZeta : ℂ → ℂ` |
| lean4export of the cone | 61.3 s | 6.14 GB | 347,115,719 bytes NDJSON |
| nanoda check (6 threads) | 35.3 s | 0.42 GB | **exit 0 — no typechecker errors** |

Export facts:

- Meta line: exporter lean4export 3.1.0, **format version 3.1.0**, produced
  from Lean **4.33.1** (githash `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`,
  the replay's pinned toolchain).
- Declaration records: **51,214** — 40,045 theorems, 10,149 definitions,
  967 inductives, 46 opaque, 4 quot, and 3 axioms: `propext`,
  `Quot.sound`, `Classical.choice` — exactly the axioms `Audit.lean`
  permits. nanoda reports "Checked 53240 declarations", counting
  constructors and recursors inside inductive groups individually.
  (An earlier version of this README said 51,211 — the counting code
  looked for axioms under a key the exporter never emits. See
  "Recount and strict-mode rerun" below.)
- SHA-256 of the reference export:
  `2e8cb9c6b6807c6583c4673368496d45c72012ef0c98c54c2379bb76bed09df6`
  (the export itself is a build artifact and is not committed; the script
  regenerates it — a second run produced the identical byte count).

nanoda's full output line was:

```
Checked 53240 declarations with no typechecker errors, 1 pretty printer errors: [
    "Unable to print axioms",
]
```

The pretty-printer error is cosmetic: it comes from nanoda's pretty
printer (`pretty_printer.rs`) being asked to print the axiom list after
checking; it is not a checking error, and the exit code is 0.

### Recount and strict-mode rerun (2026-11-20)

Two corrections to the reference run above, both prompted by review:

- **Recount.** The script counted declaration records by kind, but
  looked for axioms under the key `ax`; lean4export emits `axiom`, so
  the 3 axiom records contributed 0 to the published total. A
  record-by-record recount of the reference export (unchanged, same
  SHA-256 as above) gives **51,214** declaration records: 40,045
  theorems, 10,149 definitions, 967 inductives, 46 opaque, 4 quot,
  3 axioms. The 3 axioms are `propext`, `Quot.sound`, and
  `Classical.choice` — precisely the set `Audit.lean` permits. The
  script now counts with the corrected kind set, prints the per-kind
  breakdown, and fails loudly on any record shape it does not
  recognize, so an unrecognized kind can never again silently drop
  out of the total.
- **Strict-mode rerun.** The original run had
  `unpermitted_axiom_hard_error: false`, under which nanoda *skips*
  declarations that use an unlisted axiom, and its summary omits the
  skipped list — so the log above left open whether anything was
  skipped. The checker stage (only that stage) was rerun on the same
  export with `unpermitted_axiom_hard_error: true`, the one change to
  the configuration: **exit 0 in 36.0 s**, same "no typechecker
  errors" output. No declaration in the cone depends on an axiom
  outside the permitted set (`propext`, `Classical.choice`,
  `Quot.sound`, `Lean.trustCompiler`). The script now runs the
  checker in strict mode by default.

### Negative controls

The checker was also run on two deliberately corrupted copies of the
export, and rejected both (exit 101 in both cases):

- Swapping the *types* of two definitions: rejected while parsing
  (the NDJSON format requires expression indices to be defined before
  use; the corrupted stream violates that and the parser asserts).
- Swapping one definition's *type* and *value* fields: rejected by the
  type checker itself (`ensure_pi could not produce a pi`, `tc.rs`).

nanoda currently reports errors by panicking in its worker threads rather
than with formatted diagnostics — ugly, but the rejections are real: the
pilot's PASS is not a vacuous one.

## What this does and does not establish

It establishes that:

- Mathlib's definitions of the RH statement and of `riemannZeta`, together
  with everything those definitions transitively rest on, type-check under
  an independent kernel implementation; and
- an entire 64-module project proof packet (`P0001`: 8,914 lines of Lean,
  1,393 module-level declarations across automorphic forms, Harish-Chandra
  modules, adelic analysis, stable lattices, and abelian variety block
  theory) and its full transitive Mathlib cone also type-check cleanly in
  strict mode under `nanoda`, using only the three standard axioms
  `Audit.lean` permits.

It does **not** check the project's full proof of RH. `riemannHypothesis`
lives in the project's `Main`, which neither script imports, and no full
build of `Main` has been produced by anyone yet. Extending independent
checking to `Main` remains gated on a completed build.

## Project packet cone: `P0001` (64 modules, measured 2026-11-21)

`python3 kernel/packet_check.py <prepared-volume-dir> <packet-id> [output-dir] [--jobs N]`:

1. Verifies the pinned Lean 4.33.1 toolchain, Mathlib commit
   `0df444a360eaa60ab8c11dca51a86af692955474`, and every packet module's
   `source_sha256` from `tracker/modules.jsonl.gz`, copying sources to
   `<output-dir>/<packet-id>/src` without touching the prepared volume.
2. Compiles the packet's modules in topological order into
   `<output-dir>/<packet-id>/lib` using `lakefile.toml`'s Lean options, then
   imports all of them into `PacketRoot_<packet-id>` and inspects
   `env.header.moduleData` to collect every non-internal and user-`private`
   declaration defined by the packet's modules.
3. Exports those root declarations and their transitive dependency cone with
   `lean4export` (NDJSON 3.1.0), strictly counts every declaration record in
   the stream, and checks the export with `nanoda` in strict mode
   (`unpermitted_axiom_hard_error: true`).

Machine: AMD Ryzen 7 5800H (8 cores / 16 threads), Windows 11, 16 GB RAM.
All steps capped at 4 threads (`--jobs 4`) under shared load (another Lean
build was running concurrently on the same host).

| Step | Wall time | Peak RSS | Result |
| --- | --- | --- | --- |
| Compile 64 `P0001` modules + root (Lean 4.33.1) | 2,086.5 s | 3.69 GB | 64/64 `.olean`s built; 1,393 root declarations collected (44.1 s) |
| lean4export of `P0001` cone | 84.0 s | 4.49 GB | 772,117,861 bytes NDJSON (14,317,783 lines) |
| nanoda check (strict mode, 4 threads) | 72.8 s | 0.89 GB | **exit 0 — Checked 91,889 declarations, no typechecker errors** |

Packet `P0001` export facts:

- Packet contents (`M000001`–`M002450`, depth 0, 8,914 source lines):
  `env.header.moduleData` across the 64 modules contains 2,061 safe
  constants (`unsafe_skipped = 0`) — **1,393** root declarations passed to
  `lean4export` (1,382 public non-internal + 11 `private`) plus 668
  elaborator-generated internal auxiliaries (`_proof_*`, `_simp_*`) pulled in
  transitively where referenced. Within the 64 modules themselves: 1,189
  theorems, 800 definitions, 24 inductives, 24 constructors, 24 recursors,
  0 opaque, 0 quot, 0 axioms.
- Exported cone declaration records: **88,700** — 68,937 theorems, 18,202
  definitions, 1,497 inductives, 57 opaque, 4 quot, and 3 axioms:
  `propext`, `Quot.sound`, `Classical.choice`. `nanoda` reports
  `Checked 91889 declarations with no typechecker errors` (counting
  constructors and recursors inside inductive blocks individually) and exits
  with status 0 under `unpermitted_axiom_hard_error: true`.
- SHA-256 of the `P0001` export:
  `1681eba8c6acb56b64d47b108b96680285a0e310b4f34f358a54b53c8b05fd2a`
  (meta line: `lean4export` 3.1.0, format 3.1.0, Lean 4.33.1 githash
  `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`).

## Is a full-environment independent check plausible?

Comparing the 2-declaration statement cone (`Pilot.lean`) against the
64-module project packet cone (`P0001`):

| Metric | `Pilot.lean` (statement cone) | `P0001` (64-module packet) | Ratio |
| --- | ---: | ---: | ---: |
| Root declarations exported | 2 | 1,393 | 696.5× |
| NDJSON export size | 347,115,719 B (347.1 MB) | 772,117,861 B (772.1 MB) | **2.22×** |
| NDJSON declaration records | 51,214 | 88,700 | **1.73×** |
| `thm` / `def` / `inductive` | 40,045 / 10,149 / 967 | 68,937 / 18,202 / 1,497 | 1.72× / 1.79× / 1.55× |
| `opaque` / `quot` / `axiom` | 46 / 4 / 3 | 57 / 4 / 3 | 1.24× / 1.00× / 1.00× |
| `nanoda` checked declarations | 53,240 | 91,889 | **1.73×** |
| `lean4export` wall time | 61.3 s | 84.0 s | 1.37× |
| `nanoda` strict-mode check | 36.0 s (6 threads, 0.42 GB) | 72.8 s (4 threads, 0.89 GB) | ~1,260–1,480 decls/s |

Two takeaways stand out from scaling 2 Mathlib anchors up to 64 project
modules:

1. **Sublinear Mathlib cone growth.** Although `P0001` spans 64 modules
   across distinct areas of algebra, analysis, geometry, and representation
   theory (1,393 root declarations), the exported cone grows by only
   **1.73× in declaration records** (+37,486) and **2.22× in bytes**
   (+425 MB) over the 2-declaration `riemannZeta` cone. Roughly 97.7% of
   `P0001.ndjson`'s declarations are shared Mathlib prerequisites; the 64
   project modules themselves contribute ~2,000 constants. Because Mathlib is
   a fixed, shared base (~200k declarations total), unioning additional
   packets saturates the Mathlib portion rather than multiplying it linearly
   across all 2,858 packets; beyond the shared Mathlib base, incremental
   growth comes from the project declarations themselves.
2. **Checking remains fast and low-memory.** Once `.olean`s exist, exporting
   all 64 modules took 84 s (4.49 GB RSS) and `nanoda` checked all 91,889
   declarations in strict mode in 72.8 s using **0.89 GB RSS** on 4 threads.
   Neither `lean4export` nor `nanoda` shows superlinear blowup at packet
   scale; compiling the project `.olean`s remains the dominant cost.

## Tool pins and version coupling

All pins live in `tools.lock`. The two couplings that matter:

- **Exporter ↔ Lean version.** lean4export must be built against the
  Lean version that produced the oleans. There is no `v4.33.1` tag of
  lean4export; the reference build uses the `v4.33.0` tag's sources
  (commit `15f6055e299ad5b89345e533cc2192f4cc00f659`) built with the
  volume's Lean 4.33.1 toolchain, which worked unchanged. The export's
  meta line records the producing toolchain's githash, so this is
  auditable from the artifact itself.
- **Checker ↔ export format.** nanoda_lib 0.4.32 (commit
  `0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`) consumes NDJSON format
  version 3.1.0. (The older `ammkrn/nanoda` repository is deprecated and
  targets the pre-NDJSON text format; `nanoda_lib` is its successor.)

Lean 4.35+ toolchains bundle external checkers (nanoda, lean4lean,
others); this project's pin (4.33.1) predates that, which is why the
tools are built from pinned sources here. The same export could also be
fed to lean4lean; that was not needed for this pilot since nanoda
consumed it successfully, and it remains an obvious second opinion.

## Prerequisites

- A volume prepared by `verify.sh` (contains `elan/` and `lean/`).
- `git`, `python3`, `curl` (archive fetch is verify.sh's job, not this
  script's).
- A Rust toolchain for nanoda: `cargo` must actually run — under rustup
  that means a default toolchain is configured for the current
  `RUSTUP_HOME` (`rustup default stable`), or export
  `RUSTUP_HOME`/`CARGO_HOME` for an existing install. The script checks
  this and says so if it is missing.
- First run builds the tools from the pinned sources (~5 minutes);
  they are cached in `<output-dir>/tools`. Set `LEAN4EXPORT_BIN` /
  `NANODA_BIN` to reuse existing builds of the pinned versions.

## Layout

- `Pilot.lean` — the Mathlib-only anchor module.
- `independent-check.sh` — statement-cone pipeline; prints
  `INDEPENDENT_KERNEL_PASSED` on success.
- `packet_check.py` — packet-level pipeline (compiles any packet from
  `tracker/modules.jsonl.gz` whose project imports are built, exports all
  packet declarations and their cone with `lean4export`, and checks the
  export in strict mode with `nanoda`); prints
  `PACKET_INDEPENDENT_KERNEL_PASSED` on success.
- `test_packet_check.py` — unit tests for `packet_check.py`
  (`python3 -m unittest discover -s kernel -p 'test_*.py' -v`).
- `tools.lock` — every pin, with reference-build hashes.
- This README.
