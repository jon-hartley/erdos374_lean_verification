import OuterBoxFourierTailWork
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Absolute integrability of the averaging kernel on the entire real
frequency line. The majorant here establishes existence; sharper
logarithmic norm bounds remain in OuterBoxFourierTailWork. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace OuterKernelIntegrableWork
open OuterBoxFourierKernelWork OuterBoxFourierTailWork

theorem kernel_majorant (a b δ t : ℝ) (hδ : 0 < δ) :
    ‖smoothedKernel a b δ t‖ ≤ (|b-a|+2/δ)*(1+t^2)⁻¹ := by
  have h0 := smoothedKernel_length a b δ t hδ
  have h2 : t^2*‖smoothedKernel a b δ t‖ ≤ 2/δ := by
    by_cases ht : t=0
    · simp only [ht,zero_pow (by norm_num : 2 ≠ 0),zero_mul]
      positivity
    · have hh := smoothedKernel_second_decay a b δ t hδ ht
      have hp : 0 < t^2 := sq_pos_of_ne_zero ht
      have he : 2/(δ*t^2) = (2/δ)/t^2 := by ring
      rw [he] at hh
      have hh' := (le_div_iff₀ hp).mp hh
      nlinarith
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < 1+t^2)).mpr
  nlinarith

theorem kernel_integrable (a b δ : ℝ) (hδ : 0 < δ) :
    Integrable (smoothedKernel a b δ) := by
  apply (integrable_inv_one_add_sq.const_mul (|b-a|+2/δ)).mono'
    (kernel_continuous a b δ).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => kernel_majorant a b δ t hδ)

run_cmd do
  for decl in [``kernel_majorant, ``kernel_integrable] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterKernelIntegrableWork
