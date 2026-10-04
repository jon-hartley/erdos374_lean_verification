import OuterRampAverageWork
import Mathlib.Analysis.Fourier.Convolution

/-! The compactified source ramp is exactly a convolution of two finite
interval indicators. This supplies the spatial side of Fourier inversion. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped Convolution
namespace OuterRampConvolutionWork
open OuterRampAverageWork

def intervalBox (a b : ℝ) : ℝ → ℂ := (Ico a b).indicator (fun _ => 1)
def uniformBox (δ : ℝ) : ℝ → ℂ := (Ioc (-δ) δ).indicator (fun _ => (2*δ:ℝ)⁻¹)
def ramp (δ M : ℝ) : ℝ → ℂ := fun x => (compactRamp δ M x:ℂ)

theorem intervalBox_integrable (a b : ℝ) : Integrable (intervalBox a b) := by
  exact (integrableOn_const (μ := volume) (s := Ico a b) (C := (1:ℂ)) measure_Ico_lt_top.ne).integrable_indicator measurableSet_Ico

theorem uniformBox_integrable (δ : ℝ) : Integrable (uniformBox δ) := by
  exact (integrableOn_const (μ := volume) (s := Ioc (-δ) δ) (C := ((2*δ:ℝ):ℂ)⁻¹) measure_Ioc_lt_top.ne).integrable_indicator measurableSet_Ioc

theorem ramp_convolution (δ M : ℝ) (hδ : 0 < δ) (hM : 0 ≤ M) :
    uniformBox δ ⋆[ContinuousLinearMap.mul ℂ ℂ] intervalBox 0 M = ramp δ M := by
  ext x
  rw [convolution_mul]
  have he : (fun y => uniformBox δ y*intervalBox 0 M (x-y)) =
      (Ioc (-δ) δ).indicator (fun y => (2*δ:ℝ)⁻¹ * intervalBox 0 M (x-y)) := by
    ext y
    simp only [uniformBox,indicator_mul_left,Complex.ofReal_inv]
  rw [he,integral_indicator measurableSet_Ioc,← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_const_mul]
  have hh : (∫y in -δ..δ, intervalBox 0 M (x-y)) =
      Complex.ofReal (∫y in -δ..δ, if x-M < y ∧ y ≤ x then (1:ℝ) else 0) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro y _
    have hi : x-y ∈ Ico 0 M ↔ x-M < y ∧ y ≤ x := by
      simp only [mem_Ico]
      constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
    simp only [intervalBox,Set.indicator_apply,hi]
    split_ifs <;> simp
  rw [hh,compactRamp_interval_average δ M x hδ hM]
  simp only [ramp,Complex.ofReal_mul]
  have hz : (↑(2*δ):ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (by positivity : 0 < 2*δ))
  push_cast
  field_simp [ne_of_gt hδ]

run_cmd do
  for decl in [``intervalBox_integrable, ``uniformBox_integrable, ``ramp_convolution] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterRampConvolutionWork
