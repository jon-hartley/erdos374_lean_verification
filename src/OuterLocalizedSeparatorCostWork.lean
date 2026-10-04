import OuterActiveBlockCountWork
import OuterSourceDensityNormWork

/-! Selecting geometrically admissible rectangular blocks increases the
separator cost by at most four logarithmic powers. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace OuterLocalizedSeparatorCostWork
open OuterActiveDyadicWork OuterActiveBlockCountWork OuterSourceCubeIntegralWork
open OuterSourceDensityNormWork

theorem logarithmic_count_envelope (X : ℝ) (hX : 2 ≤ X) :
    Real.log X/Real.log 2+1 ≤ (1+(Real.log 2)⁻¹)*(1+Real.log X) := by
  have hl := Real.log_nonneg (by linarith : 1 ≤ X)
  have hi : 0 ≤ (Real.log 2)⁻¹ := (inv_pos.mpr (Real.log_pos (by norm_num))).le
  rw [div_eq_mul_inv]
  nlinarith

theorem selected_density_cost (X s T : ℝ) (hX : 2 ≤ X) (i j : ℕ) :
    (∑_k∈activeKeys X s i j, ∫ω, ‖density X s i j ω‖ ∂frequencyCube T) ≤
      ((1+(Real.log 2)⁻¹)^4*(∏n : Fin 9,coordinateConstant s i j n))*(1+Real.log X)^13 := by
  have hl : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hi : 0 ≤ (Real.log 2)⁻¹ := (inv_pos.mpr (Real.log_pos (by norm_num))).le
  have hc : ((activeKeys X s i j).card:ℝ) ≤ (1+(Real.log 2)⁻¹)^4*(1+Real.log X)^4 := by
    apply (activeKeys_card_log X s hX i j).trans
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity)
      (logarithmic_count_envelope X hX) 4
  have hD : 0 ≤ ∏n : Fin 9,coordinateConstant s i j n :=
    Finset.prod_nonneg (fun n _ => coordinateConstant_nonneg s i j n)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  calc
    _ ≤ ((1+(Real.log 2)⁻¹)^4*(1+Real.log X)^4)*
        ((∏n : Fin 9,coordinateConstant s i j n)*(1+Real.log X)^9) :=
      mul_le_mul hc (density_norm_log_bound X s T hX i j)
        (integral_nonneg (fun _ => norm_nonneg _)) (by positivity)
    _ = _ := by ring

run_cmd do
  for decl in [``logarithmic_count_envelope, ``selected_density_cost] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterLocalizedSeparatorCostWork
