import LogPhaseKernelBounds
import FlatDirichlet

/-!
An explicit bound for the actual Dirichlet Gram kernel on any integer
subinterval of (N,2N]. No kernel estimate is left as a premise.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace DirichletGramKernelBound
open Erdos374.HarmanGram152 Erdos374.HarmanAnalytic151MeanSquare

theorem kernel_log_phase (x t : ℝ) :
    exponentialKernel151 (Real.log x) t =
      Erdos374.KusminLandau151.e (LogPhaseShape.phase (t / (2 * Real.pi)) x) := by
  simpa only [neg_neg] using FlatDirichlet.kernel_log_phase x (-t)

theorem log_interval_bound (N lo hi : ℕ) (u : ℝ)
    (hN : 1 ≤ N) (hlo : N ≤ lo) (hhi : hi ≤ 2 * N) (hu : u ≠ 0) :
    ‖∑ n ∈ Finset.Ioc lo hi,
      Erdos374.KusminLandau151.e (LogPhaseShape.phase u n)‖ ≤
        8 * N / |u| + 512 * Real.sqrt (|u| * (1 + Real.log ((N : ℝ) + 1))) := by
  by_cases hempty : hi ≤ lo
  · rw [Finset.Ioc_eq_empty_of_le hempty, Finset.sum_empty, norm_zero]
    positivity
  · have hset : Finset.Ioc lo hi = Finset.Ico (lo + 1) (hi + 1) := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    rw [hset, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_add_right]
    have hh := LogPhaseKernelBounds.signed_bound N (hi - lo) ((lo : ℝ) + 1) u
      hN (by omega) (by exact_mod_cast (show N ≤ lo + 1 by omega))
      (by exact_mod_cast (show lo + 1 ≤ 2 * N by omega)) hu
    convert hh using 1
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    congr 2
    push_cast
    ring

theorem dyadic_interval_bound (N lo hi : ℕ) (t : ℝ)
    (hN : 1 ≤ N) (hlo : N ≤ lo) (hhi : hi ≤ 2 * N) (ht : t ≠ 0) :
    ‖dirichletGramKernel152 (Finset.Ioc lo hi) t‖ ≤
      64 * N / |t| + 512 * Real.sqrt (|t| * (1 + Real.log ((N : ℝ) + 1))) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hu : t / (2 * Real.pi) ≠ 0 := div_ne_zero ht hpi.ne'
  have hh := log_interval_bound N lo hi (t / (2 * Real.pi)) hN hlo hhi hu
  unfold dirichletGramKernel152
  simp_rw [kernel_log_phase]
  apply hh.trans
  rw [abs_div, abs_of_pos hpi]
  apply add_le_add
  · rw [div_div_eq_mul_div]
    apply div_le_div_of_nonneg_right _ (abs_nonneg t)
    have hp := Real.pi_lt_four
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.sqrt_le_sqrt
    have hG : 0 ≤ 1 + Real.log ((N : ℝ) + 1) := by
      have hh := Real.log_nonneg (show 1 ≤ (N : ℝ) + 1 by
        linarith [Nat.cast_nonneg (α := ℝ) N])
      linarith
    apply mul_le_mul_of_nonneg_right _ hG
    apply (div_le_iff₀ hpi).mpr
    have hp := Real.pi_gt_three
    nlinarith [abs_nonneg t]

end DirichletGramKernelBound

#print axioms DirichletGramKernelBound.dyadic_interval_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``DirichletGramKernelBound.dyadic_interval_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "DIRICHLET GRAM KERNEL BOUND PASSED"
