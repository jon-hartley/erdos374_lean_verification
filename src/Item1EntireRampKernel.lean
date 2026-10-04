import Item1LogRampSmoothing
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
No zeta-strip or prime-cap assumption occurs here.
The kernel is the parent's nonsingular product of interval integrals.
Differentiation and bounds are proved directly from the integral definition.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Item1EntireRampKernel
open Item1LogRampSmoothing

def primitive (a : ℝ) (z : ℂ) : ℂ :=
  ∫ u in (0:ℝ)..a, Complex.exp (z*(u:ℂ))

theorem primitive_set (a : ℝ) (ha : 0 ≤ a) (z : ℂ) :
    primitive a z = ∫ u in Icc (0:ℝ) a, Complex.exp (z*(u:ℂ)) := by
  rw [primitive, intervalIntegral.integral_of_le ha, integral_Icc_eq_integral_Ioc]

theorem primitive_closed (a : ℝ) (z : ℂ) (hz : z ≠ 0) :
    primitive a z = (Complex.exp (z*(a:ℂ))-1)/z := by
  simpa [primitive] using (integral_exp_mul_complex (a := (0:ℝ)) (b := a) hz)

theorem kernel_closed («λ» δ : ℝ) (z : ℂ) (hz : z ≠ 0) :
    kernel «λ» δ z =
      (Complex.exp (z*(«λ»:ℂ))-1)*(Complex.exp (z*(δ:ℂ))-1)/((δ:ℂ)*z^2) := by
  change primitive «λ» z * primitive δ z / (δ:ℂ) = _
  rw [primitive_closed «λ» z hz, primitive_closed δ z hz]
  ring

/-- Differentiation of a finite exponential integral, including z=0. -/
theorem primitive_hasDerivAt (a : ℝ) (ha : 0 ≤ a) (z : ℂ) :
    HasDerivAt (primitive a)
      (∫ u in Icc (0:ℝ) a, Complex.exp (z*(u:ℂ))*(u:ℂ)) z := by
  let μ := volume.restrict (Icc (0:ℝ) a)
  let B : ℝ := Real.exp ((‖z‖+1)*a)*a
  have hi : Integrable (fun u : ℝ => Complex.exp (z*(u:ℂ))) μ :=
    (by fun_prop : Continuous (fun u : ℝ => Complex.exp (z*(u:ℂ)))).integrableOn_Icc
  have hdi : Integrable (fun u : ℝ => Complex.exp (z*(u:ℂ))*(u:ℂ)) μ :=
    (by fun_prop : Continuous (fun u : ℝ => Complex.exp (z*(u:ℂ))*(u:ℂ))).integrableOn_Icc
  have hdom : ∀ᵐ u : ℝ ∂μ, ∀ w ∈ Metric.ball z 1,
      ‖Complex.exp (w*(u:ℂ))*(u:ℂ)‖ ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    intro w hw
    have hw' : ‖w-z‖ < 1 := by simpa [Metric.mem_ball,dist_eq_norm] using hw
    have hwn : ‖w‖ ≤ ‖z‖+1 := by
      have := norm_add_le (w-z) z
      simp only [sub_add_cancel] at this
      linarith
    have hre : w.re*u ≤ (‖z‖+1)*a := by
      have hwr : w.re ≤ ‖z‖+1 := (Complex.re_le_norm w).trans hwn
      exact (mul_le_mul_of_nonneg_right hwr hu.1).trans
        (mul_le_mul_of_nonneg_left hu.2 (by positivity))
    rw [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hu.1]
    exact mul_le_mul (Real.exp_le_exp.mpr hre) hu.2 hu.1 (Real.exp_pos _).le
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (x₀ := z) (s := Metric.ball z 1) (bound := fun _ : ℝ => B)
    (F := fun w u => Complex.exp (w*(u:ℂ)))
    (F' := fun w u => Complex.exp (w*(u:ℂ))*(u:ℂ))
    (Metric.ball_mem_nhds _ (by norm_num))
    (Filter.Eventually.of_forall (fun w =>
      (by fun_prop : Continuous (fun u : ℝ => Complex.exp (w*(u:ℂ)))).aestronglyMeasurable))
    hi hdi.aestronglyMeasurable hdom (integrable_const B)
    (Filter.Eventually.of_forall (fun u w _ => by
      simpa using ((hasDerivAt_id w).mul_const (u:ℂ)).cexp))
  have he : primitive a = fun w : ℂ => ∫ u : ℝ, Complex.exp (w*(u:ℂ)) ∂μ := by
    funext w
    exact primitive_set a ha w
  rw [he]
  exact hh.2

theorem kernel_differentiable («λ» δ : ℝ) («hλ» : 0 ≤ «λ») (hδ : 0 ≤ δ) :
    Differentiable ℂ (kernel «λ» δ) := by
  intro z
  exact (((primitive_hasDerivAt «λ» «hλ» z).mul
    (primitive_hasDerivAt δ hδ z)).div_const (δ:ℂ)).differentiableAt

theorem kernel_continuous («λ» δ : ℝ) («hλ» : 0 ≤ «λ») (hδ : 0 ≤ δ) :
    Continuous (kernel «λ» δ) := (kernel_differentiable «λ» δ «hλ» hδ).continuous

/-- Bounds for a single finite primitive are established before inversion. -/
theorem primitive_norm (a : ℝ) (ha : 0 ≤ a) (z : ℂ) (hz : z.re ≤ 1)
    (hexp : Real.exp a ≤ 2) : ‖primitive a z‖ ≤ 2*a := by
  rw [primitive_set a ha]
  have hb : ∀ u ∈ Icc (0:ℝ) a, ‖Complex.exp (z*(u:ℂ))‖ ≤ 2 := by
    intro u hu
    rw [Complex.norm_exp]
    have he : (z*(u:ℂ)).re ≤ a := by
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      exact (mul_le_mul_of_nonneg_right hz hu.1).trans (by simpa using hu.2)
    exact (Real.exp_le_exp.mpr he).trans hexp
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (measure_Icc_lt_top) hb
  simpa [Real.volume_Icc,Measure.real,ENNReal.toReal_ofReal ha,mul_comm] using h

theorem kernel_norm_small («λ» δ : ℝ) (hδ : 0 < δ) («hδλ» : δ ≤ «λ»)
    («hλ1» : «λ» ≤ 1) («hλexp» : Real.exp «λ» ≤ 2) (z : ℂ) (hz : z.re ≤ 1) :
    ‖kernel «λ» δ z‖ ≤ 4 := by
  have «hλ» : 0 ≤ «λ» := by linarith
  have hδexp : Real.exp δ ≤ 2 := (Real.exp_le_exp.mpr «hδλ»).trans «hλexp»
  have hp := primitive_norm «λ» «hλ» z hz «hλexp»
  have hq := primitive_norm δ hδ.le z hz hδexp
  change ‖primitive «λ» z*primitive δ z/(δ:ℂ)‖ ≤ 4
  rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
  apply (div_le_iff₀ hδ).mpr
  have hm := mul_le_mul hp hq (norm_nonneg _) (by positivity : 0 ≤ 2*«λ»)
  nlinarith

theorem kernel_norm_decay («λ» δ : ℝ) (hδ : 0 < δ) («hδλ» : δ ≤ «λ»)
    («hλexp» : Real.exp «λ» ≤ 2) (z : ℂ) (hz : z.re ≤ 1) (hz0 : z ≠ 0) :
    ‖kernel «λ» δ z‖ ≤ 9/(δ*‖z‖^2) := by
  have «hλ» : 0 ≤ «λ» := by linarith
  have one_bound (a : ℝ) (ha : 0 ≤ a) («haλ» : a ≤ «λ») :
      ‖Complex.exp (z*(a:ℂ))-1‖ ≤ 3 := by
    have he : ‖Complex.exp (z*(a:ℂ))‖ ≤ 2 := by
      rw [Complex.norm_exp]
      have hre : (z*(a:ℂ)).re ≤ «λ» := by
        simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
        exact (mul_le_mul_of_nonneg_right hz ha).trans (by simpa using «haλ»)
      exact (Real.exp_le_exp.mpr hre).trans «hλexp»
    have hh := norm_sub_le (Complex.exp (z*(a:ℂ))) 1
    norm_num at hh
    linarith
  rw [kernel_closed «λ» δ z hz0,norm_div,norm_mul,norm_mul,norm_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [one_bound «λ» «hλ» le_rfl,one_bound δ hδ.le «hδλ»,
    norm_nonneg (Complex.exp (z*(«λ»:ℂ))-1),
    norm_nonneg (Complex.exp (z*(δ:ℂ))-1)]

theorem kernel_vertical_bound («λ» δ c v : ℝ) (hδ : 0 < δ) («hδλ» : δ ≤ «λ»)
    («hλ1» : «λ» ≤ 1) («hλexp» : Real.exp «λ» ≤ 2) (hc : c ≤ 1) :
    ‖kernel «λ» δ ((c:ℂ)+(v:ℂ)*Complex.I)‖ ≤ 18/(δ*(1+v^2)) := by
  have hδ1 : δ ≤ 1 := «hδλ».trans «hλ1»
  have hre : (((c:ℂ)+(v:ℂ)*Complex.I):ℂ).re ≤ 1 := by simpa using hc
  have hden : 0 < δ*(1+v^2) := by positivity
  by_cases hv : |v| ≤ 1
  · have hb := kernel_norm_small «λ» δ hδ «hδλ» «hλ1» «hλexp» _ hre
    have hv2 : v^2 ≤ 1 := by nlinarith [abs_le.mp hv]
    apply hb.trans
    apply (le_div_iff₀ hden).mpr
    nlinarith [mul_le_mul hδ1 (show 1+v^2 ≤ 2 by linarith) (by positivity) (by norm_num : (0:ℝ)≤1)]
  · have hv1 : 1 < |v| := lt_of_not_ge hv
    have hv0 : v ≠ 0 := by intro hh; norm_num [hh] at hv1
    have hz0 : (c:ℂ)+(v:ℂ)*Complex.I ≠ 0 := by
      intro hh
      have := congrArg Complex.im hh
      exact hv0 (by simpa using this)
    have hnorm : v^2 ≤ ‖(c:ℂ)+(v:ℂ)*Complex.I‖^2 := by
      rw [Complex.sq_norm]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im]
      nlinarith [sq_nonneg c]
    have hb := kernel_norm_decay «λ» δ hδ «hδλ» «hλexp» _ hre hz0
    have hv2 : 1 ≤ v^2 := by nlinarith [sq_abs v]
    apply hb.trans
    apply (div_le_div_iff₀ (mul_pos hδ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hz0))) hden).mpr
    nlinarith [mul_nonneg hδ.le (show 0 ≤ 2*‖(c:ℂ)+(v:ℂ)*Complex.I‖^2-(1+v^2) by linarith)]

theorem kernel_vertical_integrable («λ» δ c : ℝ) (hδ : 0 < δ) («hδλ» : δ ≤ «λ»)
    («hλ1» : «λ» ≤ 1) («hλexp» : Real.exp «λ» ≤ 2) (hc : c ≤ 1) :
    Integrable (fun v : ℝ => kernel «λ» δ ((c:ℂ)+(v:ℂ)*Complex.I)) := by
  have hh := integrable_inv_one_add_sq.const_mul (18/δ)
  apply hh.mono' ((kernel_continuous «λ» δ (by linarith) hδ.le).comp
    (by fun_prop)).aestronglyMeasurable
  filter_upwards with v
  simpa only [Function.comp_apply, div_eq_mul_inv, mul_inv_rev,
    mul_assoc, mul_comm, mul_left_comm] using
    kernel_vertical_bound «λ» δ c v hδ «hδλ» «hλ1» «hλexp» hc

theorem kernel_vertical_norm_integral («λ» δ c : ℝ) (hδ : 0 < δ) («hδλ» : δ ≤ «λ»)
    («hλ1» : «λ» ≤ 1) («hλexp» : Real.exp «λ» ≤ 2) (hc : c ≤ 1) :
    (∫ v : ℝ, ‖kernel «λ» δ ((c:ℂ)+(v:ℂ)*Complex.I)‖) ≤ 18*Real.pi/δ := by
  have hk := kernel_vertical_integrable «λ» δ c hδ «hδλ» «hλ1» «hλexp» hc
  have hi := integrable_inv_one_add_sq.const_mul (18/δ)
  have hm := integral_mono_ae hk.norm hi (Filter.Eventually.of_forall (fun v => by
    simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using
      kernel_vertical_bound «λ» δ c v hδ «hδλ» «hλ1» «hλexp» hc))
  rw [integral_const_mul, integral_univ_inv_one_add_sq] at hm
  simpa only [div_mul_eq_mul_div] using hm

end Item1EntireRampKernel


run_cmd do
  for target in [
``Item1EntireRampKernel.primitive_set, ``Item1EntireRampKernel.primitive_closed, ``Item1EntireRampKernel.kernel_closed, ``Item1EntireRampKernel.primitive_hasDerivAt, ``Item1EntireRampKernel.kernel_differentiable, ``Item1EntireRampKernel.kernel_continuous, ``Item1EntireRampKernel.primitive_norm, ``Item1EntireRampKernel.kernel_norm_small, ``Item1EntireRampKernel.kernel_norm_decay, ``Item1EntireRampKernel.kernel_vertical_bound, ``Item1EntireRampKernel.kernel_vertical_integrable, ``Item1EntireRampKernel.kernel_vertical_norm_integral
] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
#print axioms Item1EntireRampKernel.primitive_set
#print axioms Item1EntireRampKernel.primitive_closed
#print axioms Item1EntireRampKernel.kernel_closed
#print axioms Item1EntireRampKernel.primitive_hasDerivAt
#print axioms Item1EntireRampKernel.kernel_differentiable
#print axioms Item1EntireRampKernel.kernel_continuous
#print axioms Item1EntireRampKernel.primitive_norm
#print axioms Item1EntireRampKernel.kernel_norm_small
#print axioms Item1EntireRampKernel.kernel_norm_decay
#print axioms Item1EntireRampKernel.kernel_vertical_bound
#print axioms Item1EntireRampKernel.kernel_vertical_integrable
#print axioms Item1EntireRampKernel.kernel_vertical_norm_integral




