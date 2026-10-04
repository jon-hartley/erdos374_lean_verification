# Erdős Problem #374 — Lean 4 verification

Formal verification, in Lean 4 with Mathlib, of the results of

> J. S. Hartley, M. A. Olson, J. Dhillon, *A Resolution of Erdős 374*

For `m > 1`, `F(m)` is the least `k ≥ 2` such that `a₁! a₂! ⋯ a_k!` is a perfect square for
some `1 ≤ a₁ < ⋯ < a_k = m`, and `D_k = {m > 1 : F(m) = k}`.

## What is proved

**Theorem 1.1** (`Erdos374CompleteWork.conclusions`, file `src/Erdos374CompleteWork.lean`):

* `Erdos374.MainStatement`. There is `δ > 0` such that the squarefree set `A` has density `δ`,
  `D6 ∩ B_{1/100}` has density `δ · log(100/99)`, and `D6` has lower density at least
  `δ · log(100/99) > 0`.
* `Erdos374.PositiveLowerDensity LiteratureReduction.MinimumSix`, with
  `LiteratureReduction.minimumSix_eq_D6 : MinimumSix = Erdos374.D6`.
* An explicit linear lower bound `c·N ≤ #(MinimumSix ∩ [1, N])` for all large `N`.

**Order of growth of `D3`, `D4`, `D5`, `D6`** (namespace `Erdos374.D35.Integration`,
files `src/E374/IntegrationD34.lean` and `src/E374/IntegrationD5.lean`):

| Statement | Lean theorem |
|---|---|
| `D3(X) = κ₃ √X + O(X^{2/5+ε})` for every `ε > 0` | `D3_asymptotic_closed` |
| `√X/2 ≤ D3(X) ≤ C √X` for large `X` | `D3_order_closed` |
| `D3` has density zero | `D3_densityZero_closed` |
| `D4` has lower density `≥ 1/4` | `D4_lowerDensity_closed`, `D4_order_closed` |
| `D5` has lower density `≥ log 2 / 40000` | `D5_order_closed` |
| `D6` has positive lower density | `D6_order_closed` |
| all of the above at once | `growth_summary` |

Here `κ₃ = ∑ q^{-1/2}` over the distinct values `q = sf(a!) ≠ 1` (`a ≥ 1`), so `κ₃ ≈ 2.70975`.
In Lean this is `Erdos374.D35.kappa3`.

None of these theorems has hypotheses. Every declaration listed is checked to depend only on
the standard axioms `propext`, `Classical.choice` and `Quot.sound`:

* `Erdos374CompleteWork.lean` ends with a `run_cmd` guard that fails on any other axiom.
* `src/E374/AuditIntegration.lean` and `src/E374/AuditD34.lean` run the same check on the growth
  theorems and the discharged inputs.

Both are part of the default build, so a successful `lake build` *is* the axiom audit.

## Building

Requirements: [elan](https://github.com/leanprover/elan), git, about 8 GB of RAM and a few
GB of disk.

```bash
git clone <this repository> && cd erdos374-lean
lake exe cache get        # downloads prebuilt Mathlib for the pinned commit
lake build                # builds the project (≈1000 modules) and runs the audits
```

The toolchain (`lean-toolchain`) is `leanprover/lean4:v4.35.0-rc2`. Mathlib is pinned to
`487140449b0eceeb60afe04cab75cdcaaebf227f` in `lakefile.lean` and `lake-manifest.json`.

Compiling the project modules takes roughly 2–3 CPU-hours. The largest modules
(`Erdos374_Update152` and the `UpperProfileCertificateData*` certificate tables) each need about
3.5–4.5 GB of RAM. On a machine with 8 GB, build those first, one at a time, before the
rest. The order is listed under `heavy_build_order` in `module_inventory.json`:

```bash
for m in $(python3 -c "import json;print(' '.join(json.load(open('module_inventory.json'))['heavy_build_order']))"); do
  lake build $m
done
lake build
```

To print the audit output after a build:

```bash
lake env lean src/E374/AuditIntegration.lean
```

## Layout

```
lakefile.lean            package definition; the project modules are listed explicitly
lake-manifest.json       pinned dependency revisions
module_inventory.json    module lists and the suggested build order for the heavy modules
src/                     996 modules of the proof of Theorem 1.1 (flat module names)
src/PrimeNumberTheoremAnd/ZetaBounds.lean   import shim (see THIRD_PARTY_NOTICES.md)
src/E374/                27 modules: the order-of-growth results
paper/                   the paper
THIRD_PARTY_NOTICES.md   attribution for incorporated third-party Lean code
LICENSES/Apache-2.0.txt  license text required by the incorporated Apache-2.0 code
```

The project modules keep the flat module names (`Erdos374_Update152`, `Item2ClosureWork`, …)
under which they were developed and audited, so their sources are byte-identical to the audited
ones.

### Where things are defined

* `Erdos374.HasRep`, `Erdos374.D6`, `Erdos374.sf`, `Erdos374.q`, `Erdos374.prefixCount`,
  `Erdos374.PositiveLowerDensity`, `Erdos374.MainStatement`: `src/Erdos374_Update152.lean`.
* `Erdos374.D3`, `Erdos374.D5`: `src/E374/Basic.lean`. `Erdos374.D4`: `src/E374/D4.lean`.
  All three are written exactly like the project's `D6`:
  `{m | 1 < m ∧ HasRep m k ∧ ∀ j, 2 ≤ j → j < k → ¬ HasRep m j}`.

### The growth modules

The growth proofs are written against explicit hypotheses:

* RM, `Tasks.ValuationOneMass`;
* factorial growth, `Tasks.FactorialClassGrowth`;
* a coarse Weil bound;
* almost-all short prime intervals at `θ = 11/100`;
* the uniform anchor sieve.

The theorems `D3_order`, `D3_asymptotic`, `D4_order` and `D5_order` take these as hypotheses.
`IntegrationD34.lean` and `IntegrationD5.lean` then discharge every hypothesis with theorems
already proved in the project. The short-interval estimate is re-derived from the project's
item-1 and item-2 theorems along the project's own closure chain (`harmanDyadic`).

`E374/Core.lean` imports `Erdos374_Update152`, so all statements use the project's definitions.

Mathematical outline:
* `E374/D3Short.lean` — RM forces short gaps.
* `E374/Kernel.lean`, `E374/PellClass.lean`, `E374/SmallKernel.lean` — the small-kernel count.
  `PellClass.lean` contains an elementary count for `e₁u² − e₂v² = d`.
* `E374/LargerSieve.lean`, `E374/Mertens.lean`, `E374/WeilCount.lean`, `E374/LargeKernel.lean` —
  the large-kernel count: Gallagher's larger sieve, Mertens' theorem, and a square-or-zero
  residue count.
* `E374/EBounds.lean`, `E374/EBoundsWeil.lean` — the nonconsecutive endpoint count
  `E(X) ≪ X^{2/5+ε}`.
* `E374/D3.lean`, `E374/D3Asymp.lean` — `D3`.
* `E374/D4.lean` — `D4`.
* `E374/D5Exclusion.lean`, `E374/D5Density.lean`, `E374/D5Main.lean` — `D5`.

## Verification record

On 2026-10-04 every source file in `src/` was compiled with Lean `v4.35.0-rc2` and Mathlib
`487140449b`, with 0 errors and no `sorry`. The run includes the project's final guard
(`ERDOS 374 COMPLETE: ITEMS 1 AND 2 MERGED; NO REMAINING ANALYTIC HYPOTHESES`) and the growth
audits (`AuditD34`, `AuditIntegration`). The project modules are those of the audited bundle
`erdos_progress_20261004_184509Z`, unchanged.
