import E374.D5Main
import E374.IntegrationD34
import Erdos374CompleteWork

/-!
# Discharging the D5 hypotheses, and the D6 restatement

## Harman-type almost-all short prime intervals (θ = 11/100)

The project never exports the Harman estimate on its own; it is consumed inside the
final closure chain
`Item2ClosureWork → ShortSingletonClosure → LowerHighClosure →
 DirectMovingPhysicalClosure → TailErdosClosure → PositiveSharpErdosReduction`.
Each layer, however, exposes its hypothesis transformer as a separate lemma
(`eventually_upper_negative_of_rest`, `eventually_high_negative_of_upper`,
`eventually_full_negative_of_high`, `eventually_positive_of_negative`,
`eventually_residual_transfer_log`), and the bottom layer exposes
`seed_exceptional_of_power_density`. We re-run exactly that chain with the project's
item 1 (`Item1OriginalEndpointBridge.original_source_mean`, `C_E = 1`) and item 2
(`Item2ClosureWork.item2`, `C_R = 18`), stopping at
`HarmanDyadic151.RealBackwardDyadicExceptionalMeasure151` instead of the main theorem,
and then use the project's own conversion lemmas to reach
`RemainingAnalytic21.HarmanBackwardIntervals`, which is *definitionally*
`AlmostAllShortPrimeIntervals theta`.

## Anchor sieve

`Tasks.UniformAnchorSieve` is the project's
`RemainingAnalytic141.uniformAnchor_from_coarse141 psiMediumPNT coarseHyperellipticCount`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
open Filter MeasureTheory Set

namespace Erdos374.D35.Integration

open TailRemainderMean PositiveSharpPowerWindow PositiveSharpResidual
open CancellationTransferCenter

/-- The project's real-variable dyadic exceptional-measure estimate for backward short
prime intervals, re-derived from item 1 and item 2 along the project's own chain. -/
theorem harmanDyadic : Erdos374.HarmanDyadic151.RealBackwardDyadicExceptionalMeasure151 := by
  obtain ⟨s₀, hs₀, hs1, hp⟩ :=
    TailErdosClosure.eventually_power_density_zero_positive (101 / 1000) (by norm_num) (by norm_num)
  have hs : 0 < s₀ / 2 := by positivity
  have hss : s₀ / 2 < s₀ := by linarith
  have hs1' : s₀ / 2 ≤ 1 / 1000 := by linarith
  -- item 2 (rest negative mean, `C_R = 18`) pushed down to the full negative mean
  have hR := Item2ClosureWork.item2 (s₀ / 2) hs hs1'
  have hU := ShortSingletonClosure.eventually_upper_negative_of_rest (s₀ / 2) 18 2 hs hs1' hR
  have hH := LowerHighClosure.eventually_high_negative_of_upper (s₀ / 2) (18 + 1) 2 hs hs1' hU
  have hN := DirectMovingPhysicalClosure.eventually_full_negative_of_high (s₀ / 2) (18 + 1 + 1) 2
    hs hs1' hH
  -- negative → positive one-sided mean (as in `TailErdosClosure`)
  have hP : ∀ᶠ X : ℝ in atTop,
      positiveMean X (s₀ / 2) (halfWidth X (101 / 1000)) ≤
        (18 + 1 + 1 + 1 + 1) * halfWidth X (101 / 1000) / (Real.log X) ^ 2 := by
    filter_upwards [hN, eventually_positive_of_negative (s₀ / 2) (18 + 1 + 1 + 1) 2 hs
      (hss.le.trans hs1), halfWidth_eventually (101 / 1000) (by norm_num)] with X hn hb hY
    exact (hb.2 _ hY.1.le (by linarith [hb.1, hY.2]) hn).1
  -- item 1 (source residual, `C_E = 1`) transferred to the residual
  have hE := Item1OriginalEndpointBridge.original_source_mean
  have hE' : ∀ᶠ X : ℝ in atTop,
      (∫ x in Icc X (2 * X), residualAbs X x (x * halfWidth X (101 / 1000) / X)) / X ≤
        (1 + 1) / (Real.log X) ^ 2 := by
    filter_upwards [hE, CancellationTransferResidual.eventually_residual_transfer_log 2,
      halfWidth_eventually (101 / 1000) (by norm_num)] with X he hb hY
    have hd := (abs_le.mp (hb.2 _ hY.1)).2
    have hid : ((1 : ℝ) + 1) / (Real.log X) ^ 2 = 1 / (Real.log X) ^ 2 + 1 / (Real.log X) ^ 2 := by
      ring
    rw [hid]
    linarith
  exact PositiveSharpErdosReduction.seed_exceptional_of_power_density
    (hp (s₀ / 2) hs hss (1 + 1) _ hE' hP)

/-- The project's Harman backward-interval theorem at `θ = 11/100`. -/
theorem harmanBackward : Erdos374.RemainingAnalytic21.HarmanBackwardIntervals :=
  Erdos374.RemainingAnalytic115.RemainingAnalytic127.harman_from_bad_density127
    (Erdos374.RemainingAnalytic115.RemainingAnalytic141.harman_bad_density_from_forward141
      (Erdos374.HarmanBoundary150.forward_density_from_real_measure150
        (Erdos374.HarmanAnalytic151Orientation.real_forward_from_backward151
          (Erdos374.HarmanDyadic151.backward_prefix_from_dyadic151 harmanDyadic))))

/-- **Almost all short prime intervals** at the project's `θ = 11/100`. -/
theorem shortPrimeIntervals : AlmostAllShortPrimeIntervals Erdos374.theta :=
  harmanBackward

/-- **Uniform anchor sieve** from the project. -/
theorem anchorSieve : Erdos374.Tasks.UniformAnchorSieve :=
  Erdos374.RemainingAnalytic115.RemainingAnalytic141.uniformAnchor_from_coarse141
    Erdos374.ExternalInputs149.psiMediumPNT Erdos374.ExternalInputs149.coarseHyperellipticCount

/-! ## Closed statements -/

/-- **`D5(X) ≍ X`**, unconditionally. -/
theorem D5_order_closed :
    Erdos374.PositiveLowerDensity Erdos374.D5 ∧
      ∀ X : ℕ, Erdos374.prefixCount Erdos374.D5 X ≤ X :=
  D5_order valuationOneMass factorialGrowth shortPrimeIntervals anchorSieve

open Classical in
/-- **`D6(X) ≍ X`** — the project's theorem, restated for `D6` itself. -/
theorem D6_order_closed :
    Erdos374.PositiveLowerDensity Erdos374.D6 ∧
      ∀ X : ℕ, Erdos374.prefixCount Erdos374.D6 X ≤ X := by
  refine ⟨LiteratureReduction.minimumSix_eq_D6 ▸ Erdos374CompleteWork.positive_lower_density,
    fun X => ?_⟩
  unfold Erdos374.prefixCount
  calc _ ≤ (Finset.Icc 1 X).card := Finset.card_filter_le _ _
    _ = X := by simp

/-- **Order-of-growth summary** (unconditional):
`D3(X) ≍ √X`, `D4(X) ≍ X`, `D5(X) ≍ X`, `D6(X) ≍ X`. -/
theorem growth_summary :
    (∃ C : ℝ, ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
        Real.sqrt X / 2 ≤ (Erdos374.prefixCount Erdos374.D3 X : ℝ) ∧
          (Erdos374.prefixCount Erdos374.D3 X : ℝ) ≤ C * Real.sqrt X) ∧
    (Erdos374.PositiveLowerDensity Erdos374.D4 ∧ ∀ X : ℕ, Erdos374.prefixCount Erdos374.D4 X ≤ X) ∧
    (Erdos374.PositiveLowerDensity Erdos374.D5 ∧ ∀ X : ℕ, Erdos374.prefixCount Erdos374.D5 X ≤ X) ∧
    (Erdos374.PositiveLowerDensity Erdos374.D6 ∧ ∀ X : ℕ, Erdos374.prefixCount Erdos374.D6 X ≤ X) :=
  ⟨D3_order_closed, D4_order_closed, D5_order_closed, D6_order_closed⟩

end Erdos374.D35.Integration

end
