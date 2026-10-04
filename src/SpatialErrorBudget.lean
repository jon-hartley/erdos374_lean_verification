import SignedDivisorErrorRegularity
import PolynomialLogEnvelope

/-!
Convert pointwise errors and raw contour squared means into the same
normalized spatial budget. The factor 1/(2*pi) can only reduce norms.
The final finite sum retains its factor 64 before eventual absorption.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace SpatialErrorBudget
open SignedDivisorErrorDecomposition HarmanDivisorWindow

theorem normalization_norm_le_one : ‖normalization‖ ≤ 1 := by
  unfold normalization
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity :
    (0 : ℝ) < 1 / (2 * Real.pi))]
  apply (div_le_one (by positivity : 0 < 2 * Real.pi)).mpr
  linarith [Real.pi_gt_three]

theorem normalized_norm_le (z : ℂ) : ‖normalization * z‖ ≤ ‖z‖ := by
  rw [norm_mul]
  simpa using mul_le_mul_of_nonneg_right normalization_norm_le_one (norm_nonneg z)

theorem normalize_mean_square (F : ℝ → ℂ) (X B : ℝ) (hX : 0 < X)
    (hbound : (1 / X) * (∫ x in Icc X (2 * X), ‖F x‖ ^ 2) ≤ B) :
    (1 / X) * (∫ x in Icc X (2 * X), ‖normalization * F x‖ ^ 2) ≤ B := by
  simp_rw [norm_mul, mul_pow]
  rw [integral_const_mul]
  have hnorm : ‖normalization‖ ^ 2 ≤ 1 := by
    nlinarith [normalization_norm_le_one, norm_nonneg normalization]
  have hint : 0 ≤ ∫ x in Icc X (2 * X), ‖F x‖ ^ 2 :=
    integral_nonneg (fun x => sq_nonneg _)
  apply le_trans _ hbound
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa using mul_le_mul_of_nonneg_right hnorm hint

theorem pointwise_mean_square (F : ℝ → ℂ) (X B : ℝ)
    (hX : 0 < X) (hF : IntegrableOn (fun x => ‖F x‖ ^ 2) (Icc X (2 * X)))
    (hB : ∀ x ∈ Icc X (2 * X), ‖F x‖ ≤ B) :
    (1 / X) * (∫ x in Icc X (2 * X), ‖F x‖ ^ 2) ≤ B ^ 2 := by
  have hm : (∫ x in Icc X (2 * X), ‖F x‖ ^ 2) ≤
      ∫ x in Icc X (2 * X), B ^ 2 := by
    apply integral_mono_ae hF continuous_const.integrableOn_Icc
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact pow_le_pow_left₀ (norm_nonneg _) (hB x hx) 2
  have hconst : (∫ x in Icc X (2 * X), B ^ 2) = X * B ^ 2 := by
    rw [setIntegral_const, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * X - X)]
    simp [smul_eq_mul, show 2 * X - X = X by ring]
  rw [hconst] at hm
  calc
    _ ≤ (1 / X) * (X * B ^ 2) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by field_simp

theorem error_sum_bound (s : Finset ℕ) (weight : ℕ → ℝ) (lo hi : ℕ)
    (ε X U H σ δ B : ℝ) (hs : ∀ d ∈ s, 0 < d)
    (hlo : 0 < lo) (hhi : 0 < hi) (hX : 0 < X)
    (hε : ε ∈ Ioo 0 1) (hσ : 1 < σ)
    (hδ : δ ∈ Ico 0 1) (hH : 0 ≤ H) (hHU : H ≤ U) (hUX : U ≤ X)
    (hbounds : ∀ j : Fin 8,
      (1 / X) * (∫ x in Icc X (2 * X),
        ‖errorTerms s weight lo hi ε X U H σ δ x j‖ ^ 2) ≤ B) :
    (1 / X) * (∫ x in Icc X (2 * X),
      (remainder s weight (x - x * δ) x) ^ 2) ≤ 64 * B := by
  have hh := SignedDivisorErrorRegularity.mean_square_bound s weight lo hi
    ε X U H σ δ (fun _ => B) hs hlo hhi hX hε hσ hδ hH hHU hUX hbounds
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, ← mul_assoc, show (8 : ℝ) * 8 = 64 by norm_num] using hh

theorem eventually_power_sum (c : ℝ) (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      ∀ Y R : ℝ, R ≤ 64 * (Y ^ 2 * X ^ (-c)) →
        R ≤ Y ^ 2 * X ^ (-(c / 2)) := by
  filter_upwards [PolynomialLogEnvelope.eventually_constant_bound 64 (c / 2)
    (by norm_num) (by positivity)] with X hX
  refine ⟨hX.1, ?_⟩
  intro Y R hR
  have hXp : 0 < X := by linarith [hX.1]
  apply hR.trans
  calc
    _ ≤ X ^ (c / 2) * (Y ^ 2 * X ^ (-c)) :=
      mul_le_mul_of_nonneg_right hX.2 (by positivity)
    _ = _ := by
      rw [← mul_assoc, mul_comm (X ^ (c / 2)) (Y ^ 2), mul_assoc,
        ← Real.rpow_add hXp]
      congr 2
      ring

end SpatialErrorBudget

#print axioms SpatialErrorBudget.eventually_power_sum
run_cmd do
  for target in [``SpatialErrorBudget.normalization_norm_le_one,
      ``SpatialErrorBudget.normalize_mean_square,
      ``SpatialErrorBudget.pointwise_mean_square,
      ``SpatialErrorBudget.error_sum_bound,
      ``SpatialErrorBudget.eventually_power_sum] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "SPATIAL ERROR BUDGET PASSED"
