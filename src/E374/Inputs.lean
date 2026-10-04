import E374.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Erdős 374, D3/D5 extension — named analytic inputs

These are *statements*, not proofs. Every one is either already proved in the
project's verified Lean development (`erdos_progress_20261004_184509Z`) or is a
published lemma; none is a consequence claimed by the D3/D5 draft.

Already proved in the project (discharged in `E374.Integration`):
* `Tasks.ValuationOneMass` (RM) and `Tasks.FactorialClassGrowth` (from `E374.Core`);
* `CoarseWeilBound` — exactly the statement of
  `RemainingAnalytic141.coarseDistinctCharacter_bound141` applied to
  `ExternalInputs149.coarseHyperellipticCount` (Math Inc.'s RH for hyperelliptic curves);
* `RemainingAnalytic37.AnalyticLargeSieveEnergyUpper` and
  `RemainingAnalytic37.AuxiliaryPrimeSupply` (from `E374.Core`), proved in the project
  from its additive large sieve and its PNT;
* `RemainingAnalytic123.PrimeCountRelativePNT123` (PNT, from `E374.Core`);
* `AlmostAllShortPrimeIntervals θ` for every `θ > 81/800`, from the project's closed
  Harman-type exceptional-measure theorem (conversion in `E374.Integration`).

No input outside the project is needed. (An earlier version assumed Tao's Lemma 2.10,
arXiv:2603.27990v3, for the small-kernel Pell fibres; it is replaced by the elementary
class count `pell_count_le` in `E374.PellClass`.)
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false

noncomputable section
open scoped BigOperators

namespace Erdos374.D35

/-- Coarse Weil bound for the quadratic character of a monic squarefree polynomial
split over `𝔽_p` (constant `5 deg`). This is literally the conclusion of the project's
`coarseDistinctCharacter_bound141` (with `realQuadraticChar138`, `rootProduct138`
unfolded). -/
def CoarseWeilBound : Prop :=
  ∀ p : ℕ, ∀ hp : p.Prime, p ≠ 2 →
    letI : Fact p.Prime := ⟨hp⟩
    ∀ U : Finset (ZMod p), U.Nonempty →
      |∑ x : ZMod p, ((quadraticChar (ZMod p) (∏ u ∈ U, (x - u)) : ℤ) : ℝ)| ≤
        5 * (U.card : ℝ) * Real.sqrt (p : ℝ)

/-- Almost all `m` have a prime in `[m - m^θ, m]`. For `θ = 11/100` this is literally
the project's `RemainingAnalytic21.HarmanBackwardIntervals`. -/
def AlmostAllShortPrimeIntervals (θ : ℝ) : Prop :=
  ∃ E : Set ℕ, DensityZero E ∧ ∃ N : ℕ, ∀ m : ℕ, N ≤ m → m ∉ E →
    ∃ p : ℕ, p.Prime ∧ p ≤ m ∧ ((m - p : ℕ) : ℝ) ≤ (m : ℝ) ^ θ

end Erdos374.D35

end
