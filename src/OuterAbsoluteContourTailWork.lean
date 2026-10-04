import OuterContinuousTailWork
import SmoothedFrequencySplit
import SmoothMellinMultiplier
import CofactorPowerError

/-! Absolute truncation bounds using two inverse powers of physical
frequency, independent of endpoint phase gaps. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Set Filter
namespace OuterAbsoluteContourTailWork
open MellinWindowFactor MellinSmoothingFunction OuterCenteredFlatWork

theorem compact_bound (f : ℝ→ℂ) (C H a b : ℝ) (hf : Integrable f)
    (hC : 0≤C) (hH : 0<H) (hab : a≤b) (haway : ∀t∈Icc a b,H≤|t|)
    (hcap : ∀t, H≤|t| → ‖f t‖≤C*(t^2)⁻¹) :
    ‖∫t in Icc a b,f t‖≤2*C/H := by
  have hg : IntegrableOn (fun t : ℝ => C*(t^2)⁻¹) (Icc a b) := by
    apply ContinuousOn.integrableOn_Icc
    apply continuousOn_const.mul
    exact (continuousOn_id.pow 2).inv₀ (fun t ht =>
      pow_ne_zero _ (abs_pos.mp (hH.trans_le (haway t ht))))
  have hh := (norm_integral_le_integral_norm _).trans
    (setIntegral_mono_on hf.norm.integrableOn hg measurableSet_Icc
      (fun t ht => hcap t (haway t ht)))
  rw [integral_const_mul] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left
    (OuterContinuousTailWork.inverse_square_integral a b H hab hH haway) hC).trans_eq (by ring))

theorem whole_bound (f : ℝ→ℂ) (C H : ℝ) (hf : Integrable f) (hC : 0≤C) (hH : 0<H)
    (hcap : ∀t, H≤|t| → ‖f t‖≤C*(t^2)⁻¹) :
    ‖(∫t:ℝ,f t)-(∫t in Icc (-H) H,f t)‖≤4*C/H := by
  have hp : ‖∫t in Ioi H,f t‖≤2*C/H := by
    have ht : Tendsto (fun U : ℝ => ∫t in Icc H U,f t) atTop (nhds (∫t in Ioi H,f t)) := by
      apply Tendsto.congr' _ (intervalIntegral_tendsto_integral_Ioi H hf.integrableOn tendsto_id)
      filter_upwards [eventually_ge_atTop H] with U hU
      rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hU]
      rfl
    apply le_of_tendsto (continuous_norm.continuousAt.tendsto.comp ht)
    filter_upwards [eventually_ge_atTop H] with U hU
    exact compact_bound f C H H U hf hC hH hU
      (fun t ht => ht.1.trans (le_abs_self t)) hcap
  have hn : ‖∫t in Iic (-H),f t‖≤2*C/H := by
    have ht : Tendsto (fun U : ℝ => ∫t in Icc (-U) (-H),f t) atTop (nhds (∫t in Iic (-H),f t)) := by
      apply Tendsto.congr' _ (intervalIntegral_tendsto_integral_Iic (-H) hf.integrableOn tendsto_neg_atTop_atBot)
      filter_upwards [eventually_ge_atTop H] with U hU
      rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (show -U≤-H by linarith)]
    apply le_of_tendsto (continuous_norm.continuousAt.tendsto.comp ht)
    filter_upwards [eventually_ge_atTop H] with U hU
    exact compact_bound f C H (-U) (-H) hf hC hH (by linarith)
      (fun t ht => by linarith [ht.2,neg_le_abs t]) hcap
  exact ((SmoothedFrequencySplit.whole_axis_error f H hH.le hf).trans (add_le_add hn hp)).trans_eq (by ring)

theorem mellin_bound (ε σ t : ℝ) (hε : ε∈Ioo 0 1) (hσ : 0<σ) (hσ2 : σ≤2) (ht : 0 < |t|) :
    ‖mellin (fun u => (Smooth1 smoothing ε u:ℂ)) (line σ t)‖≤4/|t| := by
  have hh := SmoothMellinMultiplier.norm_le_four smoothing ε σ t hε hσ hσ2
    differentiable nonnegative support mass_one
  have hn : |t|≤‖line σ t‖ := by simpa [line] using Complex.abs_im_le_norm (line σ t)
  unfold SmoothMellinMultiplier.multiplier at hh
  rw [norm_mul] at hh
  apply (le_div_iff₀ ht).mpr
  nlinarith [mul_le_mul_of_nonneg_right hn
    (norm_nonneg (mellin (fun u => (Smooth1 smoothing ε u:ℂ)) (line σ t)))]

theorem power_difference_bound (X x δ t : ℝ) (hX : Real.exp 1≤X)
    (hx : x∈Icc X (2*X)) (hδ : δ∈Icc 0 (1/2)) :
    ‖(x:ℂ)^line (1+1/Real.log X) t-((x-x*δ:ℝ):ℂ)^line (1+1/Real.log X) t‖≤8*X*Real.exp 1 := by
  have hXp : 0<X := (Real.exp_pos 1).trans_le hX
  have hxp : 0<x := hXp.trans_le hx.1
  have hl : 0<x-x*δ := by nlinarith [hδ.2]
  have hlx : x-x*δ≤x := by nlinarith [hδ.1]
  have hlog : 1≤Real.log X := by simpa using Real.log_le_log (Real.exp_pos 1) hX
  have hh := norm_sub_le ((x:ℂ)^line (1+1/Real.log X) t) (((x-x*δ:ℝ):ℂ)^line (1+1/Real.log X) t)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hxp,Complex.norm_cpow_eq_rpow_re_of_pos hl] at hh
  have hr : (line (1+1/Real.log X) t).re=1+1/Real.log X := by simp [line]
  rw [hr] at hh
  have hb := Real.rpow_le_rpow hl.le hlx (show 0≤1+1/Real.log X by positivity)
  have hxpow := CofactorPowerError.spatial_power_bound X x hX hx
  linarith

theorem kernel_bound (X x δ ε t : ℝ) (lo hi : ℕ) (F : ℝ→ℂ)
    (hX : Real.exp 1≤X) (hx : x∈Icc X (2*X)) (hδ : δ∈Icc 0 (1/2))
    (hε : ε∈Ioo 0 1) (hlo : 1≤lo) (hhi : 1≤hi) (ht : 0 < |t|) (hF : ‖F t‖≤1) :
    ‖F t*continuousFlat lo hi (1+1/Real.log X) t*
      mellin (fun u => (Smooth1 smoothing ε u:ℂ)) (line (1+1/Real.log X) t)*
      ((x:ℂ)^line (1+1/Real.log X) t-((x-x*δ:ℝ):ℂ)^line (1+1/Real.log X) t)‖≤
      (64*X*Real.exp 1)*(t^2)⁻¹ := by
  have hlog : 1≤Real.log X := by simpa using Real.log_le_log (Real.exp_pos 1) hX
  have hσ : 0<1+1/Real.log X := by positivity
  have hσ2 : 1+1/Real.log X≤2 := by
    have := (div_le_one (by linarith : 0<Real.log X)).mpr hlog
    linarith
  have hσ1 : 1≤1+1/Real.log X := le_add_of_nonneg_right (by positivity)
  have hc := continuousFlat_bound lo hi (1+1/Real.log X) t hlo hhi hσ1 ht
  have hm := mellin_bound ε (1+1/Real.log X) t hε hσ hσ2 ht
  have hp := power_difference_bound X x δ t hX hx hδ
  simp only [norm_mul]
  calc
    _ ≤ 1*(2/|t|)*(4/|t|)*(8*X*Real.exp 1) :=
      mul_le_mul (mul_le_mul (mul_le_mul hF hc (norm_nonneg _) (by norm_num)) hm
        (norm_nonneg _) (by positivity)) hp (norm_nonneg _) (by positivity)
    _ = _ := by rw [div_eq_mul_inv,div_eq_mul_inv,←sq_abs]; ring

run_cmd do
  for decl in [``compact_bound, ``whole_bound, ``mellin_bound, ``power_difference_bound, ``kernel_bound] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterAbsoluteContourTailWork
