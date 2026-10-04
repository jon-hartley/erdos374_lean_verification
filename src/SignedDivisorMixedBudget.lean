import SpatialErrorBudget

/-!
Combine pointwise control of four errors with squared-mean control of
the four remaining contour bands. Every quantity uses the same signed
divisor weights, endpoints, smoothing function and contour normalization.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace SignedDivisorMixedBudget
open SignedDivisorErrorDecomposition HarmanDivisorWindow HarmanDivisorContour
open SpatialErrorBudget

theorem bound (s : Finset ℕ) (weight : ℕ → ℝ) (lo hi : ℕ)
    (ε X U H σ δ sharp low trunc smooth middle upper : ℝ)
    (hs : ∀ d ∈ s, 0 < d) (hlo : 0 < lo) (hhi : 0 < hi)
    (hX : 0 < X) (hε : ε ∈ Ioo 0 1) (hσ : 1 < σ)
    (hδ : δ ∈ Ico 0 1) (hH : 0 ≤ H) (hHU : H ≤ U) (hUX : U ≤ X)
    (hsharp : ∀ x ∈ Icc X (2 * X),
      ‖error s weight lo hi ε (-X) X σ δ x‖ ≤ sharp)
    (hlow : ∀ x ∈ Icc X (2 * X),
      ‖productTransform s weight lo hi ε (-H) H σ δ x -
        continuousBand s weight lo hi ε (-H) H σ δ x‖ ≤ low)
    (htrunc : ∀ x ∈ Icc X (2 * X),
      ‖normalization * continuousBand s weight lo hi ε (-H) H σ δ x -
        smoothedMain s weight ε δ x‖ ≤ trunc)
    (hsmooth : ∀ x ∈ Icc X (2 * X),
      ‖smoothedMain s weight ε δ x - mainTerm s weight δ x‖ ≤ smooth)
    (hmidneg : (1 / X) * (∫ x in Icc X (2 * X),
      ‖productTransform s weight lo hi ε (-U) (-H) σ δ x‖ ^ 2) ≤ middle)
    (hmidpos : (1 / X) * (∫ x in Icc X (2 * X),
      ‖productTransform s weight lo hi ε H U σ δ x‖ ^ 2) ≤ middle)
    (hupneg : (1 / X) * (∫ x in Icc X (2 * X),
      ‖productTransform s weight lo hi ε (-X) (-U) σ δ x‖ ^ 2) ≤ upper)
    (huppos : (1 / X) * (∫ x in Icc X (2 * X),
      ‖productTransform s weight lo hi ε U X σ δ x‖ ^ 2) ≤ upper) :
    (1 / X) * (∫ x in Icc X (2 * X),
      remainder s weight (x - x * δ) x ^ 2) ≤
        8 * (sharp ^ 2 + low ^ 2 + trunc ^ 2 + smooth ^ 2 +
          2 * middle + 2 * upper) := by
  let budgets : Fin 8 → ℝ :=
    ![sharp ^ 2, upper, middle, low ^ 2, trunc ^ 2, smooth ^ 2, middle, upper]
  have hints := SignedDivisorErrorRegularity.errorTerms_integrable s weight lo hi
    ε X U H σ δ hs hlo hhi hX hε hσ hδ
  have hb (j : Fin 8) : (1 / X) * (∫ x in Icc X (2 * X),
      ‖errorTerms s weight lo hi ε X U H σ δ x j‖ ^ 2) ≤ budgets j := by
    fin_cases j
    · exact pointwise_mean_square _ X sharp hX (hints 0) hsharp
    · exact normalize_mean_square _ X upper hX hupneg
    · exact normalize_mean_square _ X middle hX hmidneg
    · apply pointwise_mean_square _ X low hX (hints 3)
      intro x hx
      exact (normalized_norm_le _).trans (hlow x hx)
    · exact pointwise_mean_square _ X trunc hX (hints 4) htrunc
    · exact pointwise_mean_square _ X smooth hX (hints 5) hsmooth
    · exact normalize_mean_square _ X middle hX hmidpos
    · exact normalize_mean_square _ X upper hX huppos
  have hh := SignedDivisorErrorRegularity.mean_square_bound s weight lo hi
    ε X U H σ δ budgets hs hlo hhi hX hε hσ hδ hH hHU hUX hb
  convert hh using 1
  simp [budgets, Fin.sum_univ_succ]
  ring

end SignedDivisorMixedBudget

#print axioms SignedDivisorMixedBudget.bound
run_cmd do
  let axioms ← Lean.collectAxioms ``SignedDivisorMixedBudget.bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "SIGNED DIVISOR MIXED BUDGET PASSED"
