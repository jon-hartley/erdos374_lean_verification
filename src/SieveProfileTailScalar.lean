import SieveStoppingPositiveBudget
import RosserKernelSharper

/-! Scalar estimates for a uniform bound on the actual exponential tail
beyond child ratio 20. The finite prime-sum adapter is separate. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real
namespace SieveProfileTailScalar

theorem log_le_three_eighths (x : ℝ) (hx : 0 < x) : log x ≤ (3/8:ℝ)*x := by
  have he : (8/3:ℝ) ≤ exp 1 := by
    have h := sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 1) 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    exact h
  have hl : log (8/3:ℝ) ≤ 1 := (log_le_iff_le_exp (by norm_num)).mpr he
  have h := log_le_sub_one_of_pos (show 0 < x/(8/3:ℝ) by positivity)
  rw [log_div hx.ne' (by norm_num)] at h
  linarith

theorem tail_exp_bound (t v : ℝ) (ht : 20 ≤ t) (hv : 10*v-1 ≤ t) :
    exp (-t) ≤ exp (-189/10:ℝ)*exp (1-v) := by
  rw [← exp_add]
  apply exp_le_exp.mpr
  linarith

theorem weighted_exp_bound (x v : ℝ) (hx : x ≤ 10*v) :
    x*exp (1-v) ≤ 20*exp (-v/2) := by
  have h := add_one_le_exp (v/2-1)
  have hm := mul_le_mul_of_nonneg_right h (exp_pos (1-v)).le
  have he : exp (v/2-1)*exp (1-v) = exp (-v/2) := by
    rw [← exp_add]
    congr 1
    ring
  rw [he] at hm
  have hx' := mul_le_mul_of_nonneg_right hx (exp_pos (1-v)).le
  nlinarith

theorem reciprocal_parameter_bounds (x : ℝ) (hx : (1/20:ℝ) ≤ x) :
    1/x ≤ 20 ∧ 1+2*(x+1)/x^2 ≤ 841 := by
  have hx0 : 0 < x := by linarith
  have h1 : 1/x ≤ 20 := (div_le_iff₀ hx0).mpr (by linarith)
  have hsq : (1/x)^2 ≤ (20:ℝ)^2 := pow_le_pow_left₀ (by positivity) h1 2
  have hid : 1+2*(x+1)/x^2 = 1+2*(1/x)+2*(1/x)^2 := by field_simp; ring
  rw [hid]
  exact ⟨h1, by nlinarith⟩

theorem exp_nineteen_lower : ((331/45:ℝ)^9*(12/5)) ≤ exp (189/10:ℝ) := by
  have h2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 331/45)
    SieveStoppingPositiveBudget.exp_two_lower 9
  have h09 : (12/5:ℝ) ≤ exp (9/10:ℝ) :=
    (log_le_iff_le_exp (by norm_num)).mp RosserKernelSharper.log_twelve_fifths_le
  have hh := mul_le_mul h2 h09 (by norm_num : (0:ℝ) ≤ 12/5) (by positivity)
  have he : exp 2^9*exp (9/10:ℝ) = exp (189/10:ℝ) := by
    rw [← exp_nat_mul, ← exp_add]
    norm_num
  rw [he] at hh
  exact hh

theorem final_tail_budget (e : ℝ) (_he0 : 0 ≤ e) (he : e ≤ 1/100000) :
    91*(2/5)*20*(20+841*e)*exp (-189/10:ℝ) ≤ (1/10000:ℝ) := by
  have heq : exp (-189/10:ℝ)*exp (189/10:ℝ) = 1 := by
    rw [← exp_add]
    norm_num
  have hh := mul_le_mul_of_nonneg_left exp_nineteen_lower (exp_pos (-189/10:ℝ)).le
  rw [heq] at hh
  have hinv : exp (-189/10:ℝ) ≤ 1/((331/45:ℝ)^9*(12/5)) := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ) < (331/45:ℝ)^9*(12/5))).mpr
    exact hh
  calc
    _ ≤ (91*(2/5)*20*(20+841*(1/100000:ℝ)))*(1/((331/45:ℝ)^9*(12/5))) := by
      apply mul_le_mul _ hinv (exp_pos _).le (by norm_num)
      nlinarith
    _ ≤ _ := by norm_num

run_cmd do
  for decl in [``log_le_three_eighths, ``tail_exp_bound, ``weighted_exp_bound,
    ``reciprocal_parameter_bounds, ``exp_nineteen_lower, ``final_tail_budget] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXPONENTIAL TAIL SCALAR BUDGET AT MOST 1/10000"
end SieveProfileTailScalar
end
