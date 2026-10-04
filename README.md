# Structural refinements for C7 and C13 zero-error codes

**[Read the mathematical paper (PDF)](paper/c7_c13_structural_paper.pdf)** ·
[LaTeX source](paper/main.tex) · [Lean entrypoints](lean/StructuralRelease.lean) ·
[中文摘要](summary_zh.md)

This public repository presents an exact **local C13 joint mask-allocation
theorem**, its actual graph realization, and selected formal certificates for
two existing capacity-bound constructions. The C7 correlation appendix is a
classical illustration, not a new lower-bound method.

## Main structural result

On `H = (Z/13Z)^2`, choose center and leaf masks `A, B, C` with

```
B ∩ (A ∪ (A + e1)) = ∅
C ∩ (A ∪ (A + e2)) = ∅
```

There is no leaf-to-leaf constraint. Let `a,b,c` be natural numbers, require
`|A| = a`, `|B| ≥ b`, `|C| ≥ c`, and assume **all** of

```
a + b ≤ 169,     a + c ≤ 169,
u = 169 - a - b < 13,     v = 169 - a - c < 13.
```

Such masks exist **if and only if** `min(a,169-a) ≤ u*v`. Pairwise budgets
alone miss the obstruction: `81/81/81` passes `162 ≤ 169` twice but fails
`81 ≤ 49`. An initial Ferrers diagram or its complement proves sufficiency.
The balanced optimum is **80**, attained by a 9-by-9 square minus one corner
and its two directional dilation complements.

The theorem is realized on **three actual fibers in C13^6**: a fully checked
507-point map transports arbitrary compatible masks to actual independent
sets. The balanced witness has 240 points. The two complete leaves give 338
points, so this is **not a capacity improvement**, and no global gluing is
claimed. The general-p corollary in the paper is hand-proved; the cyclic and
Ferrers Lean formalizations specialize to p=13.

## Retained capacity constructions

| Cycle | Strict formal lower bound | Dimension | Chosen prior code root |
|---|---:|---:|---:|
| C7 | Θ(C7) > 3.258834805519757 | 300 | Stavriianov: 3.258834362237710794… / 560d |
| C13 | Θ(C13) > 6.302927403571109 | 522 | Long v1.1: 6.302927071589786110… / 522d |

These bounds predate the structural round and **remain unchanged**. They are
lower bounds, not values of the unknown capacities or global-optimality results.
The exact integers and chosen-root comparisons are in
[`data/exact_roots.json`](data/exact_roots.json). C7's prior 560d size is exactly
the square of the accepted simple 280d size. C13 compares same-dimension
integers directly, not just their decimal displays.

The C7 construction uses Gao/BPZ recursion and **Tandon's heterogeneous
auxiliary sets**. The C13 improvement is a concrete **Protti guarded-cell
application on Long's DAG**. These inherited methods are not our inventions.
See [NOTICE.md](NOTICE.md) for source versions, licenses and contribution scope.

## Lean proof map

The single default build target is `StructuralRelease`.

| Claim | Source module / original endpoint | Aggregate alias |
|---|---|---|
| C7 strict capacity bound | `C7Improvement.Capacity` / `ShannonBounds.C7Improvement.shannonCapacity_C7_gt_strong` | `StructuralRelease.c7_strict` |
| C13 strict capacity bound | `ExplorationC13FrontierR03.StrictDisplay` / `ShannonBounds.ExplorationC13FrontierR03.Capacity.strict_capacity_lower` | `StructuralRelease.c13_strict` |
| Exact actual local region | `ActualRegion` / `C13Structure.actual_star_region_iff` | `StructuralRelease.c13_region` |
| Actual 240-point code | `PhysicalStar` / `C13Structure.cycleCode_independent`, `cycleCode_card` | `StructuralRelease.c13_example` |
| C7 actual correlated example | `ExplorationC7.Correlated.Witness` / `actual_union_independent` | `StructuralRelease.c7_illustration` |

Other structural modules: `MinorityRectangle`, `VoltageStar`, `StarRegion`.
`ActualRegion` proves `actual_star_upper80` and `actual_star_attains80`.
C7's `Geometry` proves classical rectangle/pair-conditioned separation and
coordinate-projection lemmas; `Witness` supplies the nonaffine literal sets,
full margins, three essential-coordinate pairs, exact size 14 and whole-block
realization. Fourteen points are weaker than the simple product's 27. The one
recorded fixed-context completion test also stopped at 27; it was not rerun
here and is not a general impossibility theorem.

Finite data are **construction inputs, not assumptions of realizability**.
The C7 side-count proofs bind C1–C4 to actual neighborhood complements; C4 uses
the ordinary `L30.Xstar`, not a modified sibling. The paper's Gao operation is
upstream `liftRPS S (flip T)`. Actual sibling identity includes I, ports and
ordered endpoint maps; equal parameter vectors would not be a substitute.

## Clean-clone reproduction

Prerequisites: a supported 64-bit Lean environment with `elan`, Git and network
access. Install the pinned toolchain through elan if necessary. The manifest
pins **Lean 4.32.2** and **mathlib
`905b95818eb32af7874a58b427f50c1711a5e96c`**. No proof caches, oleans or packages
are shipped. From a fresh clone:

```bash
git clone https://github.com/JingzheShi/odd-cycle-shannon-structural-lean.git
cd odd-cycle-shannon-structural-lean/lean
lake exe cache get
lake build StructuralRelease
```

The first command in the Lean directory resolves pinned dependencies and
downloads mathlib's build cache. The aggregate build then executes the original
selected finite certificates, including the C7 compressed side counts and
C13 Ferrers/physical/table checks. This is not a tiny arithmetic-only build;
allow time and memory for those finite computations. No search or optimization
is needed. Mathematical definitions and data are self-contained in `lean/`;
the descriptive `data/` JSON files are not read as Lean axioms.

For a W&B-logged run, authenticate to W&B and use the wrapper from repository
root (the W&B dependency is only for logging, not mathematical proofs):

```bash
python3 -c 'import wandb' 2>/dev/null || pip install wandb
export WANDB_ENTITY=YOUR_ENTITY
wandb login
bash scripts/reproduce.sh proofs
```

The wrapper records the command and return code in the W&B project
`seven-ring-shannon` and local `logs/proofs.json`.

## Paper reproduction

Use a TeX distribution containing pdfLaTeX, AMS packages, Latin Modern,
microtype and TikZ. From repository root:

```bash
bash scripts/build_paper.sh
# or, with W&B configured:
bash scripts/reproduce.sh paper
```

Both build `paper/c7_c13_structural_paper.pdf` from the supplied LaTeX sources.
All the finite recipes and certificate integers cited in the paper accompany
the repository. No private research history, environment, downloaded third-party
PDF, upload archive or unrelated cycle optimization is included.

## Validation and trust

**Publication-time validation:** exact-source accepted local compiled artifacts
were copied privately to avoid repeating expensive settled checks. Only the
**new aggregate integration target** was compiled (successful, about 1.8s).
This checks the selected namespaces and actual entrypoint types together; it
is **not** a newly executed clean-clone/full-source build. See
[`evidence/integration_validation.json`](evidence/integration_validation.json).
The Lake configuration was also loaded without rebuilding any old module.
The paper was compiled and selected theorem/table/layout pages visually checked.

**Accepted historical trust reports** are reused in `evidence/`, not rerun:

| Selected closure | Native compiler-trust dependencies |
|---|---:|
| C7 strong strict endpoint | 62 (historical six-declaration audit union: 66) |
| C13 strict capacity endpoint union | 166 = 161 new + 5 upstream |
| C13 eleven structural declarations | 9 = 6 new + 3 BPZ |
| C7 twenty illustration declarations | 8 |

The remaining reported dependencies are standard `propext`, `Classical.choice`
and `Quot.sound`, with no holes or unexpected mathematical axioms in the
accepted selected audits. Finite `native_decide` facts trust the Lean native
compiler/runtime; these are not purely kernel-arithmetic certificates. The
generic minority-rectangle and classical C7 geometry proofs use standard logic.
Audit sources are provided for readers, but are not part of a repeated
publication-time baseline audit.

## License

Apache-2.0. Existing BPZ, Long and Protti copyright/license notices are preserved;
Tandon's construction/data attribution and mathematical bibliography are in
[NOTICE.md](NOTICE.md) and the paper. New-to-project applications and examples
are distinguished from inherited methods. No worldwide novelty or capacity
breakthrough is claimed for this structural round.
