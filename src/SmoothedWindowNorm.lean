import SmoothedWindowTransfer

/-!
Pointwise and compact-integral norm bounds for the same smoothed window
kernel used by SmoothedWindowTransfer. The smoothing bound is uniform.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set

namespace SmoothedWindowNorm
open MellinWindowFactor SmoothMellinMultiplier SmoothedWindowTransfer

def kernel (ε σ δ x t : ℝ) : ℂ :=
  mellin (fun u => (Smooth1 MellinSmoothingFunction.smoothing ε u : ℂ))
    (line σ t) *
      ((x : ℂ) ^ line σ t - ((x - x * δ : ℝ) : ℂ) ^ line σ t)

theorem kernel_eq (ε σ δ x t : ℝ) (hσ : 0 < σ)
    (hx : 0 < x) (hδ : δ < 1) :
    kernel ε σ δ x t = multiplier MellinSmoothingFunction.smoothing ε σ t *
      factor σ δ t * (x : ℂ) ^ line σ t := by
  have hp := MellinWindowTransfer.power_difference x σ δ t hx hδ
  unfold kernel multiplier
  calc
    _ = (line σ t * mellin
        (fun u => (Smooth1 MellinSmoothingFunction.smoothing ε u : ℂ))
          (line σ t)) *
        (((x : ℂ) ^ line σ t - ((x - x * δ : ℝ) : ℂ) ^ line σ t) /
          line σ t) := by field_simp [line_ne_zero σ t hσ]
    _ = _ := by rw [hp]; ring

theorem kernel_bound (ε σ δ x t : ℝ) (hε : ε ∈ Ioo 0 1)
    (hσ : 1 ≤ σ) (hσtwo : σ ≤ 2) (hx : 0 < x)
    (hδ : 0 ≤ δ) (hδone : δ < 1) :
    ‖kernel ε σ δ x t‖ ≤ 4 * δ * x ^ σ := by
  have hσpos : 0 < σ := by linarith
  rw [kernel_eq ε σ δ x t hσpos hx hδone, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hre : (line σ t).re = σ := by simp [line]
  rw [hre]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx.le _)
  exact mul_le_mul
    (norm_le_four MellinSmoothingFunction.smoothing ε σ t hε hσpos hσtwo
      MellinSmoothingFunction.differentiable MellinSmoothingFunction.nonnegative
      MellinSmoothingFunction.support MellinSmoothingFunction.mass_one)
    (norm_le_width σ δ t hσ hδ hδone) (norm_nonneg _) (by norm_num)

theorem continuous_kernel (ε σ δ x : ℝ) (hε : ε ∈ Ioo 0 1)
    (hσ : 0 < σ) (hx : 0 < x) (hδone : δ < 1) :
    Continuous (kernel ε σ δ x) := by
  have heq : kernel ε σ δ x = fun t =>
      multiplier MellinSmoothingFunction.smoothing ε σ t * factor σ δ t *
        (x : ℂ) ^ line σ t := by
    funext t
    exact kernel_eq ε σ δ x t hσ hx hδone
  rw [heq]
  apply Continuous.mul
  · exact (continuous_multiplier MellinSmoothingFunction.smoothing ε σ hε hσ
      MellinSmoothingFunction.differentiable MellinSmoothingFunction.nonnegative
      MellinSmoothingFunction.support MellinSmoothingFunction.mass_one).mul
        (continuous_factor σ δ hσ hδone)
  · exact (show Continuous (line σ) by unfold line; fun_prop).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))

theorem transform_sub (F G : ℝ → ℂ) (ε a b σ δ x : ℝ)
    (hF : Continuous F) (hG : Continuous G) (hε : ε ∈ Ioo 0 1)
    (hσ : 0 < σ) (hx : 0 < x) (hδone : δ < 1) :
    transform F MellinSmoothingFunction.smoothing ε a b σ δ x -
      transform G MellinSmoothingFunction.smoothing ε a b σ δ x =
        transform (fun t => F t - G t)
          MellinSmoothingFunction.smoothing ε a b σ δ x := by
  have hkernel := continuous_kernel ε σ δ x hε hσ hx hδone
  have hleft : IntegrableOn (fun t => F t * kernel ε σ δ x t) (Icc a b) :=
    (hF.mul hkernel).integrableOn_Icc
  have hright : IntegrableOn (fun t => G t * kernel ε σ δ x t) (Icc a b) :=
    (hG.mul hkernel).integrableOn_Icc
  have hsub := integral_sub hleft hright
  simpa only [transform, kernel, sub_mul, mul_assoc] using hsub.symm

theorem transform_bound (F : ℝ → ℂ) (ε a b σ δ x B : ℝ)
    (hε : ε ∈ Ioo 0 1) (hσ : 1 ≤ σ) (hσtwo : σ ≤ 2)
    (hx : 0 < x) (hδ : 0 ≤ δ) (hδone : δ < 1) (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ‖F t‖ ≤ B) :
    ‖transform F MellinSmoothingFunction.smoothing ε a b σ δ x‖ ≤
      B * (4 * δ * x ^ σ) * (b - a) := by
  have hh := norm_setIntegral_le_of_norm_le_const
    (μ := volume) (s := Icc a b)
    (f := fun t => F t * kernel ε σ δ x t) (C := B * (4 * δ * x ^ σ))
    isCompact_Icc.measure_lt_top (by
      intro t ht
      rw [norm_mul]
      exact mul_le_mul (hF t ht) (kernel_bound ε σ δ x t hε hσ hσtwo hx hδ hδone)
        (norm_nonneg _) ((norm_nonneg _).trans (hF t ht)))
  rw [Real.volume_real_Icc_of_le hab] at hh
  simpa only [transform, kernel, mul_assoc] using hh

end SmoothedWindowNorm

#print axioms SmoothedWindowNorm.transform_bound
run_cmd do
  for target in [``SmoothedWindowNorm.kernel_bound,
      ``SmoothedWindowNorm.continuous_kernel,
      ``SmoothedWindowNorm.transform_sub,
      ``SmoothedWindowNorm.transform_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "SMOOTHED WINDOW NORM PASSED"
