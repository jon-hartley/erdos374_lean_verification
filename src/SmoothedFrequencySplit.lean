import SmoothedWindowNorm
import CompactIntegralSplit

/-!
Exact decompositions for the actual smoothed contour. Compact splits
use continuity, and the full-axis split requires absolute integrability.
Endpoint singletons have zero Lebesgue measure.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set

namespace SmoothedFrequencySplit
open SmoothedWindowTransfer SmoothedWindowNorm

theorem adjacent (F : ℝ → ℂ) (ε a b c σ δ x : ℝ)
    (hF : Continuous F) (hε : ε ∈ Ioo 0 1) (hσ : 0 < σ)
    (hx : 0 < x) (hδ : δ < 1) (hab : a ≤ b) (hbc : b ≤ c) :
    transform F MellinSmoothingFunction.smoothing ε a c σ δ x =
      transform F MellinSmoothingFunction.smoothing ε a b σ δ x +
        transform F MellinSmoothingFunction.smoothing ε b c σ δ x := by
  have hc := continuous_kernel ε σ δ x hε hσ hx hδ
  have hh := CompactIntegralSplit.split (fun t => F t * kernel ε σ δ x t)
    a b c hab hbc (hF.mul hc).integrableOn_Icc
  simpa only [transform, kernel, mul_assoc] using hh

theorem five_bands (F : ℝ → ℂ) (ε X U H σ δ x : ℝ)
    (hF : Continuous F) (hε : ε ∈ Ioo 0 1) (hσ : 0 < σ)
    (hx : 0 < x) (hδ : δ < 1) (hH : 0 ≤ H) (hHU : H ≤ U) (hUX : U ≤ X) :
    transform F MellinSmoothingFunction.smoothing ε (-X) X σ δ x =
      transform F MellinSmoothingFunction.smoothing ε (-X) (-U) σ δ x +
      transform F MellinSmoothingFunction.smoothing ε (-U) (-H) σ δ x +
      transform F MellinSmoothingFunction.smoothing ε (-H) H σ δ x +
      transform F MellinSmoothingFunction.smoothing ε H U σ δ x +
      transform F MellinSmoothingFunction.smoothing ε U X σ δ x := by
  rw [adjacent F ε (-X) (-U) X σ δ x hF hε hσ hx hδ (by linarith) (by linarith),
    adjacent F ε (-U) (-H) X σ δ x hF hε hσ hx hδ (by linarith) (by linarith),
    adjacent F ε (-H) H X σ δ x hF hε hσ hx hδ (by linarith) (by linarith),
    adjacent F ε H U X σ δ x hF hε hσ hx hδ hHU hUX]
  ring

theorem whole_axis (f : ℝ → ℂ) (H : ℝ) (hH : 0 ≤ H) (hf : Integrable f) :
    (∫ t : ℝ, f t) =
      (∫ t in Iic (-H), f t) + (∫ t in Icc (-H) H, f t) +
        ∫ t in Ioi H, f t := by
  have hh := intervalIntegral.integral_Iic_sub_Iic
    (hf.integrableOn (s := Iic (-H))) (hf.integrableOn (s := Iic H))
  rw [intervalIntegral.integral_of_le (by linarith : -H ≤ H),
    ← integral_Icc_eq_integral_Ioc] at hh
  have hu := intervalIntegral.integral_Iic_add_Ioi
    (hf.integrableOn (s := Iic H)) (hf.integrableOn (s := Ioi H))
  rw [← hu]
  linear_combination hh

theorem whole_axis_error (f : ℝ → ℂ) (H : ℝ)
    (hH : 0 ≤ H) (hf : Integrable f) :
    ‖(∫ t : ℝ, f t) - (∫ t in Icc (-H) H, f t)‖ ≤
      ‖∫ t in Iic (-H), f t‖ + ‖∫ t in Ioi H, f t‖ := by
  rw [whole_axis f H hH hf]
  convert norm_add_le (∫ t in Iic (-H), f t) (∫ t in Ioi H, f t) using 1
  congr 1
  ring

end SmoothedFrequencySplit

#print axioms SmoothedFrequencySplit.whole_axis_error
run_cmd do
  for target in [``SmoothedFrequencySplit.adjacent,
      ``SmoothedFrequencySplit.five_bands,
      ``SmoothedFrequencySplit.whole_axis,
      ``SmoothedFrequencySplit.whole_axis_error] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "SMOOTHED FREQUENCY SPLIT PASSED"
