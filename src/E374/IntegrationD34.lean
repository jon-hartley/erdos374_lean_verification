import E374.D3
import E374.D3Asymp
import E374.D4
import PositiveSharpErdosClosure

/-!
# Discharging the D3 / D4 hypotheses with the project's closed theorems

Every input below is a theorem already proved (with only the standard axioms) in the
project `erdos_progress_20261004_184509Z`:

* `psiMediumPNT`               — `Erdos374.ExternalInputs149.psiMediumPNT`
  (PNT with a medium error term, flattened from PrimeNumberTheoremAnd);
* `coarseHyperellipticCount`   — `Erdos374.ExternalInputs149.coarseHyperellipticCount`
  (RH for hyperelliptic curves over `𝔽_p`, coarse form);
* `polynomial_sampling`        — `PositiveSharpErdosClosure.polynomial_sampling`
  (large-phase Mangoldt cancellation, the checked sampling chain).

From these the project derives RM (`Tasks.ValuationOneMass`), factorial growth
(`Tasks.FactorialClassGrowth`) and the coarse Weil character bound; we only re-assemble
them with the same terms the project uses in `core18_from_remaining141`.

After this, every statement below is unconditional: no input outside the project is
used (the small-kernel Pell fibres are handled by the elementary class count
`pell_count_le`, so Tao's Lemma 2.10 is not needed).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Erdos374.D35.Integration

open Erdos374

/-- The project's θ-remainder from PNT (`RemainingAnalytic134`). -/
theorem thetaRemainder : RemainingAnalytic115.RemainingAnalytic127.ThetaLogSqRemainder127 :=
  RemainingAnalytic115.RemainingAnalytic134.thetaLogSqRemainder_from_mediumPNT134
    ExternalInputs149.psiMediumPNT

/-- **RM**, assembled exactly as in the project's `core18_from_remaining141`. -/
theorem valuationOneMass : Tasks.ValuationOneMass :=
  RemainingAnalytic44.valuationOneMass_from_hardened
    (denseBranch_from_topIntervalMass
      (RemainingAnalytic115.denseTopIntervalPrimeMass_from_logMass115
        (RemainingAnalytic115.RemainingAnalytic119.denseTopLogPrimeMass_from_theta119
          (RemainingAnalytic115.RemainingAnalytic127.denseTopThetaMass_from_thetaRemainder127
            thetaRemainder))))
    (RemainingAnalytic115.RemainingAnalytic127.sparseWeightedTransfer_from_count127
      (RemainingAnalytic115.RemainingAnalytic141.sparseGoodPrimeCount_from_sublog141
        ExternalInputs149.psiMediumPNT 4
        (SamplingPolynomial149.sparseSublog_from_polynomial_sampling
          PositiveSharpErdosClosure.polynomial_sampling)))

/-- **Factorial growth** `q_a ≥ e^{a/3}` eventually. -/
theorem factorialGrowth : Tasks.FactorialClassGrowth :=
  factorial_growth_of_log_q
    (RemainingAnalytic115.RemainingAnalytic130.logQGrowth_from_theta130 thetaRemainder)

/-- **Coarse Weil bound**, from the project's hyperelliptic point count. -/
theorem coarseWeil : CoarseWeilBound := by
  intro p hp hp2
  letI : Fact p.Prime := ⟨hp⟩
  intro U hU
  have h := RemainingAnalytic115.RemainingAnalytic141.coarseDistinctCharacter_bound141
    ExternalInputs149.coarseHyperellipticCount p hp hp2 U hU
  simpa only [RemainingAnalytic115.RemainingAnalytic138.realQuadraticChar138,
    RemainingAnalytic115.RemainingAnalytic138.rootProduct138] using h

/-! ## Closed statements -/

/-- **`D3` has density zero**, unconditionally. -/
theorem D3_densityZero_closed : DensityZero D3 :=
  D3_densityZero valuationOneMass factorialGrowth

/-- **`D3(X) ≍ √X`**, unconditionally. -/
theorem D3_order_closed :
    ∃ C : ℝ, ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      Real.sqrt X / 2 ≤ (prefixCount D3 X : ℝ) ∧ (prefixCount D3 X : ℝ) ≤ C * Real.sqrt X :=
  D3_order valuationOneMass factorialGrowth coarseWeil

/-- **`D3(X) = κ₃ √X + O(X^{2/5+ε})`**, unconditionally. -/
theorem D3_asymptotic_closed :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      |(prefixCount D3 X : ℝ) - kappa3 * Real.sqrt X| ≤ C * (X : ℝ) ^ ((2 : ℝ) / 5 + ε) :=
  D3_asymptotic valuationOneMass factorialGrowth coarseWeil

/-- **`D4(X) ≍ X`**, unconditionally (lower density `≥ 1/4`). -/
theorem D4_order_closed : PositiveLowerDensity D4 ∧ ∀ X : ℕ, prefixCount D4 X ≤ X :=
  D4_order valuationOneMass factorialGrowth

/-- Explicit form: `D4` has lower density at least `1/4`. -/
theorem D4_lowerDensity_closed : LowerDensityAtLeast D4 (1 / 4) :=
  D4_lowerDensity valuationOneMass factorialGrowth

end Erdos374.D35.Integration

end
