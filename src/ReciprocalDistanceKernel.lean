import CompactIntegral

/-!
The explicit logarithmic row integral of 1/(1+|t-u|). This majorizes the
correlation kernel for Fourier integration over an interval of length <=1.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Set

namespace ReciprocalDistanceKernel

def kernel (t u : ℝ) : ℝ := (1 + |t - u|)⁻¹

theorem nonnegative (t u : ℝ) : 0 ≤ kernel t u := by unfold kernel; positivity

theorem symmetric (t u : ℝ) : kernel t u = kernel u t := by
  unfold kernel
  rw [abs_sub_comm]

theorem continuous_kernel : Continuous kernel.uncurry := by
  unfold kernel Function.uncurry
  exact (continuous_const.add (continuous_fst.sub continuous_snd).abs).inv₀
    (fun p => by
      change 1 + |p.1 - p.2| ≠ 0
      positivity)

theorem continuous_row (t : ℝ) : Continuous (kernel t) :=
  continuous_kernel.comp (continuous_const.prodMk continuous_id)

theorem left_integral (a t : ℝ) (hat : a ≤ t) :
    (∫ u in a..t, kernel t u) = Real.log (1 + t - a) := by
  have hi : IntervalIntegrable (kernel t) volume a t :=
    (continuous_row t).intervalIntegrable a t
  have hd : ∀ u ∈ uIcc a t,
      HasDerivAt (fun v => -Real.log (1 + t - v)) (kernel t u) u := by
    intro u hu
    have hu' : a ≤ u ∧ u ≤ t := by simpa only [uIcc_of_le hat, mem_Icc] using hu
    have hp : 0 < 1 + t - u := by linarith
    have hh := (((hasDerivAt_const u (1 + t)).sub (hasDerivAt_id u)).log hp.ne').neg
    convert hh using 1
    · rfl
    · unfold kernel
      rw [abs_of_nonneg (by linarith : 0 ≤ t - u)]
      simp only [Pi.sub_apply, id_eq, zero_sub, neg_div, neg_neg, one_div]
      congr 1; ring
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  simpa only [show 1 + t - t = 1 by ring, Real.log_one, neg_zero, zero_sub,
    neg_neg] using hh

theorem right_integral (t b : ℝ) (htb : t ≤ b) :
    (∫ u in t..b, kernel t u) = Real.log (1 + b - t) := by
  have hi : IntervalIntegrable (kernel t) volume t b :=
    (continuous_row t).intervalIntegrable t b
  have hd : ∀ u ∈ uIcc t b,
      HasDerivAt (fun v => Real.log (1 + v - t)) (kernel t u) u := by
    intro u hu
    have hu' : t ≤ u ∧ u ≤ b := by simpa only [uIcc_of_le htb, mem_Icc] using hu
    have hp : 0 < 1 + u - t := by linarith
    have hh := (((hasDerivAt_id u).const_add 1).sub_const t).log hp.ne'
    convert hh using 1
    · rfl
    · unfold kernel
      rw [abs_of_nonpos (by linarith : t - u ≤ 0)]
      simp only [id_eq, one_div]
      congr 1; ring
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  simpa only [show 1 + t - t = 1 by ring, Real.log_one, sub_zero] using hh

theorem row_bound (a b t : ℝ) (ht : t ∈ Icc a b) :
    (∫ u in Icc a b, kernel t u) ≤ 2 * Real.log (1 + b - a) := by
  have hc : Continuous (kernel t) := continuous_row t
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (ht.1.trans ht.2),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable a t) (hc.intervalIntegrable t b),
    left_integral a t ht.1, right_integral t b ht.2]
  have hl := Real.log_le_log (by linarith [ht.1] : 0 < 1 + t - a)
    (show 1 + t - a ≤ 1 + b - a by linarith [ht.2])
  have hr := Real.log_le_log (by linarith [ht.2] : 0 < 1 + b - t)
    (show 1 + b - t ≤ 1 + b - a by linarith [ht.1])
  linarith

end ReciprocalDistanceKernel

#print axioms ReciprocalDistanceKernel.row_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``ReciprocalDistanceKernel.row_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "RECIPROCAL DISTANCE KERNEL PASSED"
