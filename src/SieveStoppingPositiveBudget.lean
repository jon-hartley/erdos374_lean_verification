import SieveStoppingSharpContraction

/-! A rationally certified positive margin at the proposed first cutoff.
This scalar budget does not by itself supply the actual stopping envelope. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Real
namespace SieveStoppingPositiveBudget

theorem exp_two_lower : (331/45:ℝ) ≤ exp 2 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 2) 7
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

theorem exp_shift_bound (r : ℝ) (hr : (105/26:ℝ) ≤ r) :
    exp (2-r) ≤ (130/993:ℝ) := by
  have hlin : (27/26:ℝ) ≤ exp (r-4) := by
    have h := Real.add_one_le_exp (r-4)
    linarith
  have hmul := mul_le_mul exp_two_lower hlin (by norm_num : (0:ℝ) ≤ 27/26)
    (exp_pos 2).le
  have hprod : exp 2*exp (r-4) = exp (r-2) := by
    rw [← exp_add]
    congr 1
    ring
  rw [hprod] at hmul
  have hid : exp (2-r)*exp (r-2) = 1 := by
    rw [← exp_add, show (2-r)+(r-2)=0 by ring, exp_zero]
  have h := mul_le_mul_of_nonneg_left hmul (exp_pos (2-r)).le
  rw [hid] at h
  nlinarith

theorem exp_negative_bound (r : ℝ) (hr : (105/26:ℝ) ≤ r) :
    exp (-r) ≤ (1/49:ℝ) := by
  have h4 : (49:ℝ) ≤ exp 4 := by
    have h := mul_le_mul exp_two_lower exp_two_lower (by norm_num : (0:ℝ) ≤ 331/45)
      (exp_pos 2).le
    rw [← exp_add] at h
    norm_num at h
    linarith
  have hr4 : (49:ℝ) ≤ exp r := h4.trans (exp_le_exp.mpr (by linarith))
  have hid : exp (-r)*exp r = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
  have h := mul_le_mul_of_nonneg_left hr4 (exp_pos (-r)).le
  rw [hid] at h
  linarith

theorem normalized_loss_budget (r : ℝ) (hr : (105/26:ℝ) ≤ r) :
    91*(exp (-r)*(RosserKernelContraction.majorant r+1/500)) ≤ (49/50:ℝ) := by
  have hr4 : ¬r ≤ 4 := by linarith
  simp only [RosserKernelContraction.majorant, hr4, ite_false]
  have hd : (105/26:ℝ)*(79/26) ≤ r*(r-1) := by nlinarith
  have hmain : exp (2-r)/(r*(r-1)) ≤ (130/993:ℝ)/((105/26)*(79/26)) :=
    div_le_div₀ (by norm_num) (exp_shift_bound r hr) (by norm_num) hd
  have he := exp_negative_bound r hr
  have hid : exp (-r)*exp 2 = exp (2-r) := by
    rw [← exp_add]
    congr 1
    ring
  calc
    _ = 91*(exp (2-r)/(r*(r-1))+exp (-r)/500) := by
      rw [show exp (-r)*(exp 2/(r*(r-1))+1/500) =
        (exp (-r)*exp 2)/(r*(r-1))+exp (-r)/500 by ring, hid]
    _ ≤ 91*((130/993:ℝ)/((105/26)*(79/26))+(1/49)/500) := by
      have hh := add_le_add hmain (div_le_div_of_nonneg_right he (by norm_num : (0:ℝ) ≤ 500))
      exact mul_le_mul_of_nonneg_left hh (by norm_num)
    _ ≤ _ := by norm_num

run_cmd do
  for decl in [``exp_two_lower, ``exp_shift_bound, ``exp_negative_bound,
    ``normalized_loss_budget] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "FIRST CUTOFF SCALAR LOSS BUDGET AT MOST 49/50 PASSED"
end SieveStoppingPositiveBudget
end
