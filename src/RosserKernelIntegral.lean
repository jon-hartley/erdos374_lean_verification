import RosserKernelContraction
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The continuous two-step Rosser kernel has an exponential-weight contraction.
This module does not assert a transfer from discrete prime stopping sums. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology
namespace RosserKernelIntegral

def kernel (r t : ℝ) : ℝ := exp (-t) * log ((t+1)/(r-1))
def cutoff (r : ℝ) : ℝ := max 2 (r-2)
def weightedMass (r : ℝ) : ℝ :=
  exp r / r * ∫ t in Ioi (cutoff r), kernel r t

theorem ramp_deriv (a t : ℝ) :
    HasDerivAt (fun x : ℝ => -exp (-x)*(x-a+1)) (exp (-t)*(t-a)) t := by
  convert! (((hasDerivAt_id t).neg.exp).neg.mul
    (((hasDerivAt_id t).sub_const a).add_const 1)) using 1
  all_goals solve | rfl | (dsimp; ring)

theorem ramp_limit (a : ℝ) :
    Tendsto (fun t : ℝ => -exp (-t)*(t-a+1)) atTop (𝓝 0) := by
  have hp : Tendsto (fun t : ℝ => t*exp (-t)) atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) 1 (by norm_num)
  have he : Tendsto (fun t : ℝ => exp (-t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have h := hp.neg.add (he.const_mul (a-1))
  simp only [neg_zero, mul_zero, add_zero] at h
  convert h using 1
  ext t
  ring

theorem ramp_integrable (a : ℝ) :
    IntegrableOn (fun t : ℝ => exp (-t)*(t-a)) (Ioi a) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun t _ => ramp_deriv a t)
    (fun _t ht => mul_nonneg (exp_pos _).le (sub_nonneg.mpr ht.le)) (ramp_limit a)

theorem ramp_integral (a : ℝ) :
    (∫ t in Ioi a, exp (-t)*(t-a)) = exp (-a) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (fun t _ => ramp_deriv a t)
    (fun t ht => mul_nonneg (exp_pos _).le (sub_nonneg.mpr ht.le)) (ramp_limit a)
  simpa using h

theorem log_tangent (r a t : ℝ) (hr : 1 < r) (ha : 0 < a+1) (ht : a ≤ t) :
    log ((t+1)/(r-1)) ≤ log ((a+1)/(r-1)) + (t-a)/(a+1) := by
  have htp : 0 < t+1 := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos htp ha)
  rw [Real.log_div htp.ne' ha.ne'] at h
  rw [Real.log_div htp.ne' (by linarith), Real.log_div ha.ne' (by linarith)]
  have hid : (t+1)/(a+1)-1 = (t-a)/(a+1) := by field_simp; ring
  rw [hid] at h
  linarith

theorem kernel_nonneg (r a t : ℝ) (hr : 1 < r) (ha : r-2 ≤ a) (ht : a ≤ t) :
    0 ≤ kernel r t := by
  apply mul_nonneg (exp_pos _).le
  apply Real.log_nonneg
  exact (one_le_div (by linarith)).mpr (by linarith)

theorem kernel_integral_bound (r a : ℝ) (hr : 1 < r) (ha : 0 < a+1)
    (hra : r-2 ≤ a) :
    IntegrableOn (kernel r) (Ioi a) ∧
      (∫ t in Ioi a, kernel r t) ≤
        exp (-a)*(log ((a+1)/(r-1))+1/(a+1)) := by
  let L := log ((a+1)/(r-1))
  let g := fun t : ℝ => L*exp (-t) + (1/(a+1))*(exp (-t)*(t-a))
  have hg : IntegrableOn g (Ioi a) :=
    ((integrableOn_exp_neg_Ioi a).const_mul L).add ((ramp_integrable a).const_mul _)
  have hle : ∀ t ∈ Ioi a, kernel r t ≤ g t := by
    intro t ht
    have h := mul_le_mul_of_nonneg_left (log_tangent r a t hr ha ht.le) (exp_pos (-t)).le
    dsimp [kernel, g, L] at *
    convert h using 1
    ring
  have hc : ContinuousOn (kernel r) (Ioi a) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    unfold kernel
    apply ContinuousAt.mul (by fun_prop)
    apply ContinuousAt.log (by fun_prop)
    apply div_ne_zero (by linarith [ht.out]) (by linarith)
  have hi : IntegrableOn (kernel r) (Ioi a) := hg.mono'
    (hc.aestronglyMeasurable measurableSet_Ioi) (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg r a t hr hra ht.le)]
      exact hle t ht)
  refine ⟨hi, (setIntegral_mono_on hi hg measurableSet_Ioi hle).trans_eq ?_⟩
  change (∫ t in Ioi a, L*exp (-t)+(1/(a+1))*(exp (-t)*(t-a))) = _
  rw [integral_add ((integrableOn_exp_neg_Ioi a).const_mul L)
    ((ramp_integrable a).const_mul _), integral_const_mul, integral_const_mul,
    integral_exp_neg_Ioi, ramp_integral]
  dsimp [L]
  ring

theorem kernel_integrable (r : ℝ) (hr : 2 ≤ r) :
    IntegrableOn (kernel r) (Ioi (cutoff r)) :=
  (kernel_integral_bound r (cutoff r) (by linarith)
    (by have h := le_max_left (2 : ℝ) (r-2); dsimp [cutoff]; linarith)
    (le_max_right _ _)).1

theorem weightedMass_le_majorant (r : ℝ) (hr : 2 ≤ r) :
    weightedMass r ≤ RosserKernelContraction.majorant r := by
  have hrp : 0 < r := by linarith
  have h := (kernel_integral_bound r (cutoff r) (by linarith)
    (by have h := le_max_left (2 : ℝ) (r-2); dsimp [cutoff]; linarith)
    (le_max_right _ _)).2
  have hm := mul_le_mul_of_nonneg_left h (div_nonneg (exp_pos r).le hrp.le)
  unfold weightedMass
  apply hm.trans_eq
  unfold RosserKernelContraction.majorant
  split_ifs with h4
  · have hc : cutoff r = 2 := max_eq_left (by linarith)
    rw [hc]
    norm_num
    rw [show exp r / r * (exp (-2) * (log (3/(r-1))+1/3)) =
      (exp r * exp (-2))/r * (log (3/(r-1))+1/3) by ring,
      ← Real.exp_add]
    congr 2
  · have hc : cutoff r = r-2 := max_eq_right (by linarith)
    rw [hc]
    have hden : r-1 ≠ 0 := by linarith
    rw [show r-2+1 = r-1 by ring, div_self hden, Real.log_one, zero_add]
    rw [show exp r / r * (exp (-(r-2)) * (1/(r-1))) =
      (exp r * exp (-(r-2)))/(r*(r-1)) by field_simp,
      ← Real.exp_add, show r + -(r-2) = 2 by ring]

theorem weightedMass_le (r : ℝ) (hr : 2 ≤ r) : weightedMass r ≤ 99/100 :=
  (weightedMass_le_majorant r hr).trans (RosserKernelContraction.majorant_le r hr)

run_cmd do
  for decl in [``ramp_deriv, ``ramp_limit, ``ramp_integrable, ``ramp_integral,
    ``log_tangent, ``kernel_nonneg, ``kernel_integral_bound, ``kernel_integrable,
    ``weightedMass_le_majorant, ``weightedMass_le] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end RosserKernelIntegral
end
