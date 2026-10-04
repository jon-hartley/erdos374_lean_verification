import SieveProfileStaircase
import SieveProfileTailScalar

/-! A target-row staircase bound remains valid at every larger ratio,
up to a uniform bound on the separately appended exponential tail. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real
open scoped BigOperators
namespace SieveProfileUniformBound
open SieveProfileStaircase

theorem staircase_antitone (N : ℕ) (v : ℕ → ℝ)
    (hd : ∀ j < N, 0 ≤ v j-v (j+1)) : Antitone (staircase N v) := by
  intro r s hrs
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (hd j (Finset.mem_range.mp hj))
  by_cases hs : s ≤ cut j
  · have hr := hrs.trans hs
    simp only [hs, hr, ite_true, le_refl]
  · simp only [hs, ite_false]
    split_ifs <;> norm_num

theorem staircase_target (v : ℕ → ℝ) (hN : v 90=0) :
    staircase 90 v (105/26:ℝ)=v 10 := by
  have hh := profile_target v hN
  simpa only [profile, SieveProfileExponentialTail.tail,
    show ¬(20:ℝ) ≤ 105/26 by norm_num, ite_false, add_zero] using hh

theorem exp_twenty_lower : (910000:ℝ) ≤ exp 20 := by
  calc
    _ ≤ (331/45:ℝ)^9*(12/5) := by norm_num
    _ ≤ exp (189/10:ℝ) := SieveProfileTailScalar.exp_nineteen_lower
    _ ≤ exp 20 := exp_le_exp.mpr (by norm_num)

theorem tail_at_twenty : 91*exp (-20:ℝ) ≤ (1/10000:ℝ) := by
  rw [exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (exp_pos 20)).mpr
  linarith [exp_twenty_lower]

theorem tail_bound (r : ℝ) : SieveProfileExponentialTail.tail r ≤ (1/10000:ℝ) := by
  unfold SieveProfileExponentialTail.tail
  split_ifs with hr
  · exact (mul_le_mul_of_nonneg_left
      (exp_le_exp.mpr (neg_le_neg hr)) (by norm_num : (0:ℝ) ≤ 91)).trans tail_at_twenty
  · norm_num

theorem profile_le_target_plus_tail (v : ℕ → ℝ)
    (hd : ∀ j < 90, 0 ≤ v j-v (j+1)) (hN : v 90=0)
    (r : ℝ) (hr : (105/26:ℝ) ≤ r) :
    profile 90 v r ≤ v 10+1/10000 := by
  have hs := (staircase_antitone 90 v hd hr).trans_eq (staircase_target v hN)
  exact add_le_add hs (tail_bound r)

run_cmd do
  for decl in [``staircase_antitone, ``staircase_target, ``exp_twenty_lower,
    ``tail_at_twenty, ``tail_bound, ``profile_le_target_plus_tail] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "UNIFORM STAIRCASE BOUND ABOVE TARGET RATIO WITH SMALL EXPONENTIAL TAIL"

end SieveProfileUniformBound
end
