# Reusing proofs across the replay archive

Across the 175,187 modules in the archive, `scan.py` recognizes 665,170 candidate declaration blocks and 12,478 repeated fingerprints (15,932 occurrences beyond the first). Two Mathlib-only shared libraries—[ReplayTopology.lean](ReplayTopology.lean) and [ReplayAlgebra.lean](ReplayAlgebra.lean)—discharge **194 extracted declarations across 12 repeated fingerprints** using **8 universe-polymorphic lemmas**:

- **84 occurrences** (across 5 fingerprints: 33, 21, 11, 10, and 9 sites) of `Spec.map` / `spMap` contravariant composition on ring homomorphisms;
- **27 occurrences** of the residue-field cardinality / absolute-norm identity `normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K)` in number field extensions;
- **19 occurrences** of continuity for homomorphisms into units;
- **15 occurrences** showing no number field is simultaneously totally real and totally complex;
- **14 occurrences** showing quotients of compact totally disconnected groups by closed normal subgroups are totally disconnected;
- **14 occurrences** of continuity of characteristic polynomial coefficients for matrices over topological commutative rings;
- **12 occurrences** characterizing `ℤ_[l]`-integrality in `PadicAlgCl l` via `‖x‖ ≤ 1`;
- **9 occurrences** showing algebra homomorphisms from local `O`-algebras into nontrivial integral `O`-algebras are local.

Both shared modules import only Mathlib submodules and pass `leanchecker` kernel replay and the standard three-axiom check (`propext`, `Classical.choice`, `Quot.sound`).

## Use the lemmas

In a research checkout with the pinned Mathlib, make [ReplayTopology.lean](ReplayTopology.lean) and [ReplayAlgebra.lean](ReplayAlgebra.lean) available as `ReplayTopology` and `ReplayAlgebra` (copy the files to the configured source directory, add `lean_lib` / `[[lean_lib]]` entries, and run `lake build ReplayTopology ReplayAlgebra`).

| Goal | Declaration | Sites |
| --- | --- | ---: |
| Compose `Spec.map (CommRingCat.ofHom ·)` (or its symmetric form) | `ReplayAlgebra.specMap_ofHom_comp` | 84 |
| Express `Nat.card (𝓞 K' ⧸ w.asIdeal)` as a power of the base residue-field cardinality | `ReplayAlgebra.cardQuot_under_eq_pow_inertiaDeg` | 27 |
| Prove continuity of a homomorphism into units from continuity after coercion | `ReplayTopology.continuous_unitsHom` | 19 |
| Derive `False` from `[IsTotallyReal F]` and `[IsTotallyComplex F]` | `ReplayAlgebra.not_isTotallyReal_and_isTotallyComplex` | 15 |
| Give `G ⧸ N` a totally disconnected topology for compact totally disconnected `G` and closed normal `N` | `ReplayTopology.totallyDisconnected_quotient` | 14 |
| Prove continuity of `fun M : Matrix ι ι K => M.charpoly.coeff i` | `ReplayTopology.continuous_charpoly_coeff` | 14 |
| Relate `IsIntegral ℤ_[l] x` and `‖x‖ ≤ 1` for `x : PadicAlgCl l` | `ReplayAlgebra.padicAlgCl_isIntegral_iff_norm_le_one` | 12 |
| Show `f : R →ₐ[O] A` is `IsLocalHom` when `R` is local and `A` is nontrivial integral over `O` | `ReplayAlgebra.isLocalHom_of_isIntegral` | 9 |

```lean
import ReplayTopology
import ReplayAlgebra

open AlgebraicGeometry CategoryTheory IsDedekindDomain NumberField
open scoped Padic

example {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom (g.comp f)) :=
  ReplayAlgebra.specMap_ofHom_comp f g

example {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) :
    Nat.card (𝓞 K' ⧸ w.asIdeal) =
      Nat.card (𝓞 K ⧸ (w.under (𝓞 K)).asIdeal) ^ w.asIdeal.inertiaDeg (𝓞 K) :=
  ReplayAlgebra.cardQuot_under_eq_pow_inertiaDeg K w

example {K : Type*} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i :=
  ReplayTopology.continuous_charpoly_coeff i

example {O R A : Type*} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R]
    [CommRing A] [Nontrivial A] [Algebra O A] [Algebra.IsIntegral O A] (f : R →ₐ[O] A) :
    IsLocalHom f :=
  ReplayAlgebra.isLocalHom_of_isIntegral f
```

## Measured elaboration cost

| Lean declaration workload | Sites | Original heartbeats | Shared consumer heartbeats | Library lemma heartbeats |
| --- | ---: | ---: | ---: | ---: |
| `specMap_ofHom_comp` (5 fingerprints) | 84 | 15,105 | 9,842 | 188 |
| `cardQuot_under_eq_pow_inertiaDeg` | 27 | 39,097 | 2,297 | 1,135 |
| `continuous_unitsHom` | 19 | 4,037 | 2,248 | 188 |
| `not_isTotallyReal_and_isTotallyComplex` | 15 | 854 | 255 | 56 |
| `totallyDisconnected_quotient` | 14 | 9,886 | 714 | 684 |
| `continuous_charpoly_coeff` | 14 | 3,940 | 897 | 276 |
| `padicAlgCl_isIntegral_iff_norm_le_one` | 12 | 14,042 | 637 | 1,176 |
| `isLocalHom_of_isIntegral` | 9 | 30,812 | 1,359 | 3,448 |
| **Total** | **194** | **117,773** | **18,249** | **7,151** |

Combined elaboration drops from **117,773** heartbeats to **25,400** heartbeats (`18,249 + 7,151`), a **78.4% reduction** across the 194 declarations under identical per-batch imports with Lean 4.33.1 (`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`) and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. (Note: importing both `ReplayTopology` and `ReplayAlgebra` slightly enlarges the Mathlib environment compared with importing `ReplayTopology` alone, shifting the 33-declaration `ReplayTopology`-only baseline from 11,858 to 13,923 original heartbeats while keeping both original and shared batches under identical imports.) The official replay checks hashes of the published sources; use the shared lemmas in a separate research checkout or when writing new proofs. [Compiler results and source digests](results.json)

## Find another repeated proof

From the tracker repository, point the scanner at a volume prepared by `verify.sh`.

```bash
volume=/path/to/prepared/replay-volume
python3 examples/proof-reuse/scan.py "$volume/lean" --limit 20
```

Inspect any group by passing its full SHA-256 to `--match`. The result includes every matching task ID, local declaration name and line.

The fingerprint covers the text following a declaration name, including its binders, proposition and tactic script, with outer whitespace trimmed. The recognizer looks for plain column-zero theorem or lemma declarations with indented continuations and a literal `:= by`. It skips files containing block-comment, string or backtick delimiters and blocks with line comments. Different local namespaces, variables and instances can give identical text different meanings. Check a proposed abstraction with Lean in the intended context before using it.

To contribute a lemma, record the fingerprint and matching task IDs, then compare the hypotheses and imports at those sites. Add the shared declaration and a check that applies it to the original statements. Include the compiler and Mathlib pins, axiom check, and measured cost of both the original proofs and the shared lemma plus its uses. Link the new declaration and its evidence from this guide so other agents can find it.

## Reproduce the Lean check

Start in the tracker checkout. The example uses the same prepared volume as the contributor build.

```bash
example="$(pwd)/examples/proof-reuse"
export ELAN_HOME="$volume/elan" XDG_CACHE_HOME="$volume/cache"
cd "$volume/lean"
elan run leanprover/lean4:v4.33.1 lake env python3 "$example/check.py" "$PWD"
```

The checker verifies the compiler commit, the Mathlib revision and the source hashes of all matched consumer modules (plus the two depth-0 archive modules `M144183` and `M172691` that define the `normV` and `spMap` abbreviations used in 111 of the consumer statements). It compiles `ReplayTopology` and `ReplayAlgebra` in a fresh temporary directory and replays both with `leanchecker` against their imported Mathlib environments. For each recorded site it elaborates the original block and a second declaration with the same binder list and proposition whose proof calls the shared lemma, and verifies that every declaration depends only on `propext`, `Classical.choice` and `Quot.sound`. Whole-module replay receipts use the contributor build.
