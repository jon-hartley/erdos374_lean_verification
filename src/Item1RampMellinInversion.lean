import Item1RampFourier
import Item1RampLineDefinitions
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Tactic

/-!
Exact full-line inversion of the parent's actual continuous ramp.
No inversion identity is a theorem parameter. All qualitative hypotheses of
Mathlib's Fourier inversion are filled by the preceding kernel/convolution lemmas.
-/
set_option autoImplicit false
set_option maxHeartbeats 18000000
noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform
namespace Item1RampMellinInversion
open Item1LogRampSmoothing Item1EntireRampKernel Item1RampFourier

def inverseIntegrand («λ» δ c u v : ℝ) : ℂ :=
  Complex.exp (-line c v*(u:ℂ))*kernel «λ» δ (line c v)

theorem inverse_norm («λ» δ c u v : ℝ) :
    ‖inverseIntegrand «λ» δ c u v‖ =
      Real.exp (-c*u)*‖kernel «λ» δ (line c v)‖ := by
  simp [inverseIntegrand,line,Complex.norm_exp,Complex.mul_re]

theorem inverse_integrable («λ» δ c u : ℝ) (hδ : 0 < δ) («hδλ» : δ ≤ «λ»)
    («hλ1» : «λ» ≤ 1) («hλexp» : Real.exp «λ» ≤ 2) (hc : c ≤ 1) :
    Integrable (inverseIntegrand «λ» δ c u) := by
  have hk := kernel_vertical_integrable «λ» δ c hδ «hδλ» «hλ1» «hλexp» hc
  have hi := hk.norm.const_mul (Real.exp (-c*u))
  apply hi.mono' (by
    unfold inverseIntegrand line
    exact ((by fun_prop : Continuous (fun v : ℝ =>
      Complex.exp (-((c:ℂ)+(v:ℂ)*Complex.I)*(u:ℂ)))).mul
      ((kernel_continuous «λ» δ (by linarith) hδ.le).comp (by fun_prop))).aestronglyMeasurable)
  filter_upwards with v
  exact (inverse_norm «λ» δ c u v).le

theorem fourier_tilted_integrable («λ» δ c : ℝ) (hδ : 0 < δ) («hδλ» : δ ≤ «λ»)
    («hλ1» : «λ» ≤ 1) («hλexp» : Real.exp «λ» ≤ 2) (hc : c ≤ 1) :
    Integrable (𝓕 (tilted «λ» δ c)) := by
  have hk := kernel_vertical_integrable «λ» δ c hδ «hδλ» «hλ1» «hλexp» hc
  have hs := hk.comp_mul_left' (show (-2*Real.pi:ℝ) ≠ 0 by positivity)
  convert hs using 1
  funext ξ
  rw [fourier_tilted «λ» δ c ξ hδ «hδλ»]
  congr 1
  push_cast
  ring

/-- Full infinite inversion, including all ramp endpoints and c=0. -/
theorem weight_inversion («λ» δ c u : ℝ) (hδ : 0 < δ) («hδλ» : δ ≤ «λ»)
    («hλ1» : «λ» ≤ 1) («hλexp» : Real.exp «λ» ≤ 2) (hc : c ≤ 1) :
    (weight «λ» δ u:ℂ) = (1/(2*Real.pi):ℝ) *
      (∫ v : ℝ, inverseIntegrand «λ» δ c u v) := by
  have hfi := tilted_integrable «λ» δ c hδ «hδλ»
  have hF := fourier_tilted_integrable «λ» δ c hδ «hδλ» «hλ1» «hλexp» hc
  have hinv := hfi.fourierInv_fourier_eq hF (v := u) (tilted_continuous «λ» δ c).continuousAt
  rw [Real.fourierInv_eq_fourier_neg,Real.fourier_real_eq_integral_exp_smul] at hinv
  simp_rw [fourier_tilted «λ» δ c _ hδ «hδλ»] at hinv
  let J : ℝ → ℂ := fun v => Complex.exp (-(v:ℂ)*Complex.I*(u:ℂ))*kernel «λ» δ (line c v)
  have he : (∫ ξ : ℝ,
      Complex.exp ((-2*Real.pi*ξ*(-u):ℝ)*Complex.I) •
        kernel «λ» δ ((c:ℂ)-(2*Real.pi*ξ:ℝ)*Complex.I)) =
      ∫ ξ : ℝ, J ((-2*Real.pi)*ξ) := by
    apply integral_congr_ae
    filter_upwards with ξ
    dsimp [J,line]
    congr 2 <;> push_cast <;> ring
  rw [he,Measure.integral_comp_mul_left] at hinv
  have ha : |(-2*Real.pi:ℝ)⁻¹| = 1/(2*Real.pi) := by
    rw [abs_inv,abs_of_neg (by nlinarith [Real.pi_pos])]
    ring
  rw [ha,Complex.real_smul] at hinv
  have hexp : Complex.exp (-((c:ℂ)*(u:ℂ))) * tilted «λ» δ c u = (weight «λ» δ u:ℂ) := by
    unfold tilted
    rw [←mul_assoc,←Complex.exp_add]
    simp
  rw [←hexp,←hinv]
  have hpoint (v : ℝ) :
      Complex.exp (-((c:ℂ)*(u:ℂ)))*J v = inverseIntegrand «λ» δ c u v := by
    unfold J inverseIntegrand line
    rw [←mul_assoc,←Complex.exp_add]
    congr 2
    ring
  calc
    _ = ((1/(2*Real.pi):ℝ):ℂ) *
        (Complex.exp (-((c:ℂ)*(u:ℂ)))*(∫ v : ℝ, J v)) := by ring
    _ = _ := by rw [←integral_const_mul]; simp_rw [hpoint]

theorem inverse_norm_integral («λ» δ c u : ℝ) (hδ : 0 < δ) («hδλ» : δ ≤ «λ»)
    («hλ1» : «λ» ≤ 1) («hλexp» : Real.exp «λ» ≤ 2) (hc : c ≤ 1) :
    (∫ v : ℝ, ‖inverseIntegrand «λ» δ c u v‖) =
      Real.exp (-c*u)*(∫ v : ℝ, ‖kernel «λ» δ (line c v)‖) := by
  simp_rw [inverse_norm]
  exact integral_const_mul _ _

end Item1RampMellinInversion

run_cmd do
  for target in [``Item1RampMellinInversion.inverse_norm,
    ``Item1RampMellinInversion.inverse_integrable,
    ``Item1RampMellinInversion.fourier_tilted_integrable,
    ``Item1RampMellinInversion.weight_inversion,
    ``Item1RampMellinInversion.inverse_norm_integral] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Item1RampMellinInversion.weight_inversion
