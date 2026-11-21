# Optional check of the Galois restriction homomorphism

This example compares task M115085 in packet P0048 (`CovariantDegrees`) with a shorter version of the same module ([`CovariantDegrees.lean`](CovariantDegrees.lean)). Given a number field `E`, an algebraic closure `Ω` of `ℚ` over `E`, an embedding `j : Ω →+* PadicAlgCl l`, and a valuation subring `A` of `Ω` cut out by `‖j x‖ ≤ 1`, the module restricts elements of the `l`-adic fixing subgroup `(KwF j).fixingSubgroup` to the decomposition subgroup `ValuationSubring.decompositionSubgroup E A` and proves Krull continuity of the resulting homomorphism `rHom` (`continuous_rHom`). For instance, an 878-line multiplicativity lemma (`conj_invariant_character_transport`) collapses to 12 lines, and the 778-line `MonoidHom` construction `rHom` collapses to 11 lines. Across the module the source falls from 6,170 to 214 lines (96.5%).

The [audit](AuditAll.lean) compares all 25 public declarations using `rfl`, verifies that no non-private declaration from the published module is omitted, checks their argument names, order, visibility and universes, and checks axiom dependencies across all 25 declarations with `collectAxioms`. For definitions this checks the resulting values. Theorems are compared by their propositions, using proof irrelevance. The full comparison and `leanchecker` replay passed on Lean 4.33.1 (`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`) with the pinned Mathlib objects (`0df444a360eaa60ab8c11dca51a86af692955474`), reporting only `propext`, `Classical.choice` and `Quot.sound`. With the same eight imports, synchronous elaboration (`-j1 -DElab.async=false`) of the 25 public declarations used 37,478 heartbeats before and 13,911 afterward (48,990 vs. 15,072 including `private` helper declarations). [Pin, source digests and results](receipt.json) · [Lean 4.33.1 compiler and `leanchecker` transcript](transcript.txt)

Start in the root of a clean checkout of this repository on Linux. Set `volume` below to the absolute path of the replay volume prepared with `./verify.sh /path/to/new/replay-volume --prepare-only` as described in the [contributor guide](../../CONTRIBUTING.md#build-a-task). You can reuse an existing prepared volume.

```bash
example="$(pwd)/examples/M115085/replay.py"
volume=/path/to/prepared/replay-volume
export ELAN_HOME="$volume/elan" XDG_CACHE_HOME="$volume/cache"
cd "$volume/lean"
elan run leanprover/lean4:v4.33.1 lake env python3 "$example" "$PWD"
```

Instead of storing a multi-thousand-line patch file in the repository, [`make_diff.py`](make_diff.py) deterministically regenerates the unified diff between the pinned archive source and [`CovariantDegrees.lean`](CovariantDegrees.lean) and checks its SHA-256 digest (`python3 examples/M115085/make_diff.py "$volume/lean" -o covariant_degrees.patch`). `replay.py` verifies the published source, compressed source, regenerated diff, reference wrapper, and audit file against [`receipt.json`](receipt.json), compiles all three Lean modules in a temporary directory, and replays them with `leanchecker`. To check only the source and diff digests without invoking Lean, run `python3 examples/M115085/replay.py "$volume/lean" --sources-only` from the checkout root. This check covers M115085. The volunteer build and fresh-kernel checks for the published archive run through the existing replay workflow.
