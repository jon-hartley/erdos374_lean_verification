import HarmanProductTail

/-! A finite-height oscillatory resolvent estimate for the continuous cofactor endpoints. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set

namespace OscillatoryResolvent

def denominator (a t : ℝ) : ℂ := (a : ℂ) - Complex.I * (t : ℂ)
def phase (φ t : ℝ) : ℂ := Complex.exp (Complex.I * ((φ * t : ℝ) : ℂ))
private def primitive (φ t : ℝ) : ℂ := phase φ t * (Complex.I * (φ : ℂ))⁻¹

private theorem denominator_ne_zero (a t : ℝ) (ht : 0 < t) : denominator a t ≠ 0 := by
  intro h
  have hh := congrArg Complex.im h
  simp [denominator] at hh
  linarith

private theorem denominator_norm_ge (a t : ℝ) (ht : 0 ≤ t) :
    t ≤ ‖denominator a t‖ := by
  have hh := Complex.abs_im_le_norm (denominator a t)
  simp [denominator, abs_of_nonneg ht] at hh
  exact hh

private theorem derivative_denominator (a t : ℝ) :
    HasDerivAt (denominator a) (-Complex.I) t := by
  have hcast : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 t := by
    simpa using (hasDerivAt_id (t : ℂ)).comp_ofReal
  change HasDerivAt (fun z : ℝ => (a : ℂ) - Complex.I * (z : ℂ))
    (-Complex.I) t
  simpa using (hcast.const_mul Complex.I).const_sub (a : ℂ)

private theorem derivative_resolvent (a t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun z => (denominator a z)⁻¹)
      (Complex.I / (denominator a t) ^ 2) t := by
  convert (derivative_denominator a t).inv (denominator_ne_zero a t ht) using 1
  ring

private theorem derivative_phase (φ t : ℝ) :
    HasDerivAt (phase φ)
      (phase φ t * (Complex.I * (φ : ℂ))) t := by
  have hcast : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 t := by
    simpa using (hasDerivAt_id (t : ℂ)).comp_ofReal
  have hinner : HasDerivAt (fun z : ℝ => Complex.I * ((φ * z : ℝ) : ℂ))
      (Complex.I * (φ : ℂ)) t := by
    convert (hcast.const_mul ((φ : ℂ) * Complex.I)) using 1 <;> push_cast <;> ring
  change HasDerivAt (fun z : ℝ => Complex.exp
      (Complex.I * (((φ * z : ℝ) : ℂ))))
    (Complex.exp (Complex.I * (((φ * t : ℝ) : ℂ))) *
      (Complex.I * (φ : ℂ))) t
  exact hinner.cexp

private theorem phase_norm (φ t : ℝ) : ‖phase φ t‖ = 1 := by
  simp [phase, Complex.norm_exp]

private theorem frequency_ne_zero (φ : ℝ) (hφ : φ ≠ 0) :
    Complex.I * (φ : ℂ) ≠ 0 := by
  exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hφ)

private theorem derivative_primitive (φ t : ℝ) (hφ : φ ≠ 0) :
    HasDerivAt (primitive φ) (phase φ t) t := by
  have hh := (derivative_phase φ t).mul_const (Complex.I * (φ : ℂ))⁻¹
  convert hh using 1
  · rfl
  · have hφC : (φ : ℂ) ≠ 0 := by exact_mod_cast hφ
    field_simp [frequency_ne_zero φ hφ, hφC]

private theorem primitive_norm (φ t : ℝ) (_hφ : φ ≠ 0) :
    ‖primitive φ t‖ = |φ|⁻¹ := by
  rw [primitive, norm_mul, phase_norm, one_mul, norm_inv, norm_mul,
    Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

private theorem inverse_square_integral (H U : ℝ) (hH : 0 < H) (hHU : H ≤ U) :
    (∫ t in H..U, (t ^ 2)⁻¹) = H⁻¹ - U⁻¹ := by
  have hcont : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Icc H U) := by
    apply ContinuousOn.inv₀ (continuousOn_id.pow 2)
    intro t ht
    have htpos : 0 < t := hH.trans_le ht.1
    exact pow_ne_zero 2 htpos.ne'
  have hderiv : ∀ t ∈ uIcc H U,
      HasDerivAt (fun z : ℝ => -z⁻¹) ((t ^ 2)⁻¹) t := by
    intro t ht
    have ht' : t ∈ Icc H U := by simpa only [uIcc_of_le hHU] using ht
    have htpos : 0 < t := hH.trans_le ht'.1
    convert (hasDerivAt_inv htpos.ne').neg using 1
    ring
  have hci : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (uIcc H U) := by
    simpa only [uIcc_of_le hHU] using hcont
  simpa [sub_eq_add_neg, add_comm] using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hci.intervalIntegrable

private theorem inverse_square_integral_le (H U : ℝ) (hH : 0 < H) (hHU : H ≤ U) :
    (∫ t in H..U, (t ^ 2)⁻¹) ≤ H⁻¹ := by
  rw [inverse_square_integral H U hH hHU]
  have hU : 0 < U := hH.trans_le hHU
  have : 0 ≤ U⁻¹ := inv_nonneg.mpr hU.le
  linarith

private theorem resolvent_norm_le (a t : ℝ) (ht : 0 < t) :
    ‖(denominator a t)⁻¹‖ ≤ t⁻¹ := by
  rw [norm_inv]
  simpa only [one_div] using
    one_div_le_one_div_of_le ht (denominator_norm_ge a t ht.le)

private theorem resolvent_derivative_norm_le (a t : ℝ) (ht : 0 < t) :
    ‖Complex.I / (denominator a t) ^ 2‖ ≤ (t ^ 2)⁻¹ := by
  rw [norm_div, Complex.norm_I, norm_pow]
  simpa only [one_div] using one_div_le_one_div_of_le (sq_pos_of_pos ht)
    (pow_le_pow_left₀ ht.le (denominator_norm_ge a t ht.le) 2)

private theorem continuous_denominator (a : ℝ) : Continuous (denominator a) := by
  unfold denominator
  fun_prop

private theorem continuous_phase (φ : ℝ) : Continuous (phase φ) :=
  continuous_iff_continuousAt.mpr (fun t => (derivative_phase φ t).continuousAt)

private theorem continuous_primitive (φ : ℝ) (hφ : φ ≠ 0) :
    Continuous (primitive φ) :=
  continuous_iff_continuousAt.mpr
    (fun t => (derivative_primitive φ t hφ).continuousAt)

theorem bound (a φ H U : ℝ) (hφ : φ ≠ 0) (hH : 0 < H) (hHU : H ≤ U) :
    ‖∫ t in H..U, phase φ t / denominator a t‖ ≤
      4 / (|φ| * H) := by
  let resolvent := fun t : ℝ => (denominator a t)⁻¹
  let derivative := fun t : ℝ => Complex.I / (denominator a t) ^ 2
  have hpositive : ∀ t ∈ Icc H U, 0 < t := by
    intro t ht
    exact hH.trans_le ht.1
  have hnonzero : ∀ t ∈ Icc H U, denominator a t ≠ 0 := by
    intro t ht
    exact denominator_ne_zero a t (hpositive t ht)
  have hrescont : ContinuousOn resolvent (Icc H U) := by
    exact (continuous_denominator a).continuousOn.inv₀ hnonzero
  have hdercont : ContinuousOn derivative (Icc H U) := by
    exact continuousOn_const.div ((continuous_denominator a).continuousOn.pow 2)
      (fun t ht => pow_ne_zero 2 (hnonzero t ht))
  have hu : ∀ t ∈ uIcc H U, HasDerivAt resolvent (derivative t) t := by
    intro t ht
    exact derivative_resolvent a t (hpositive t (by simpa only [uIcc_of_le hHU] using ht))
  have hv : ∀ t ∈ uIcc H U, HasDerivAt (primitive φ) (phase φ t) t := by
    intro t ht
    exact derivative_primitive φ t hφ
  have hdui : IntervalIntegrable derivative volume H U := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hHU] using hdercont
  have hdvi : IntervalIntegrable (phase φ) volume H U := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hHU] using (continuous_phase φ).continuousOn
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hdui hdvi
  have hshape : (∫ t in H..U, phase φ t / denominator a t) =
      resolvent U * primitive φ U - resolvent H * primitive φ H -
        ∫ t in H..U, derivative t * primitive φ t := by
    convert hparts using 1
    · apply intervalIntegral.integral_congr
      intro t ht
      simp [resolvent, div_eq_mul_inv, mul_comm]
  have hφpos : 0 < |φ| := abs_pos.mpr hφ
  have hUpos : 0 < U := hH.trans_le hHU
  have hUinv : U⁻¹ ≤ H⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hH hHU
  have hendU : ‖resolvent U * primitive φ U‖ ≤ H⁻¹ * |φ|⁻¹ := by
    rw [norm_mul, primitive_norm φ U hφ]
    exact mul_le_mul_of_nonneg_right
      ((resolvent_norm_le a U hUpos).trans hUinv) (by positivity)
  have hendH : ‖resolvent H * primitive φ H‖ ≤ H⁻¹ * |φ|⁻¹ := by
    rw [norm_mul, primitive_norm φ H hφ]
    exact mul_le_mul_of_nonneg_right (resolvent_norm_le a H hH) (by positivity)
  have hmajor : IntervalIntegrable (fun t : ℝ => |φ|⁻¹ * (t ^ 2)⁻¹)
      volume H U := by
    apply ContinuousOn.intervalIntegrable
    have hc : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Icc H U) := by
      apply ContinuousOn.inv₀ (continuousOn_id.pow 2)
      intro t ht
      exact pow_ne_zero 2 (hpositive t ht).ne'
    have hconst : ContinuousOn (fun _ : ℝ => |φ|⁻¹) (Icc H U) :=
      continuousOn_const
    have hh := hconst.mul hc
    have hheq : ((fun _ : ℝ => |φ|⁻¹) * fun t : ℝ => (t ^ 2)⁻¹) =
        (fun t : ℝ => |φ|⁻¹ * (t ^ 2)⁻¹) := by
      funext t
      rfl
    rw [hheq] at hh
    simpa only [uIcc_of_le hHU] using hh
  have hderiv_bound :
      ‖∫ t in H..U, derivative t * primitive φ t‖ ≤
        H⁻¹ * |φ|⁻¹ := by
    calc
      _ ≤ ∫ t in H..U, ‖derivative t * primitive φ t‖ :=
        intervalIntegral.norm_integral_le_integral_norm hHU
      _ ≤ ∫ t in H..U, |φ|⁻¹ * (t ^ 2)⁻¹ := by
        apply intervalIntegral.integral_mono_on hHU
        · apply ContinuousOn.intervalIntegrable
          simpa only [uIcc_of_le hHU, Pi.mul_apply] using
            (hdercont.mul (continuous_primitive φ hφ).continuousOn).norm
        · exact hmajor
        · intro t ht
          rw [norm_mul, primitive_norm φ t hφ]
          simpa only [mul_comm] using mul_le_mul_of_nonneg_right
            (resolvent_derivative_norm_le a t (hpositive t ht))
            (inv_nonneg.mpr hφpos.le)
      _ = |φ|⁻¹ * (∫ t in H..U, (t ^ 2)⁻¹) := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ |φ|⁻¹ * H⁻¹ :=
        mul_le_mul_of_nonneg_left (inverse_square_integral_le H U hH hHU)
          (by positivity)
      _ = _ := by ring
  rw [hshape]
  calc
    _ ≤ ‖resolvent U * primitive φ U‖ +
        ‖resolvent H * primitive φ H‖ +
          ‖∫ t in H..U, derivative t * primitive φ t‖ := by
            calc
              _ ≤ ‖resolvent U * primitive φ U - resolvent H * primitive φ H‖ +
                    ‖∫ t in H..U, derivative t * primitive φ t‖ := by
                      exact norm_sub_le
                        (resolvent U * primitive φ U - resolvent H * primitive φ H)
                        (∫ t in H..U, derivative t * primitive φ t)
              _ ≤ _ := add_le_add
                (norm_sub_le (resolvent U * primitive φ U)
                  (resolvent H * primitive φ H)) le_rfl
    _ ≤ H⁻¹ * |φ|⁻¹ + H⁻¹ * |φ|⁻¹ + H⁻¹ * |φ|⁻¹ := by
      exact add_le_add (add_le_add hendU hendH) hderiv_bound
    _ ≤ 4 / (|φ| * H) := by
      have : 0 ≤ H⁻¹ * |φ|⁻¹ := by positivity
      field_simp [hH.ne', hφpos.ne']
      nlinarith

end OscillatoryResolvent

#print axioms OscillatoryResolvent.bound
run_cmd do
  let axioms ← Lean.collectAxioms ``OscillatoryResolvent.bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "OSCILLATORY RESOLVENT PASSED"
