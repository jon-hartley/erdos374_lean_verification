import RosserKernelContraction

/-! Rational quarter-mesh improvement of the continuous scalar majorant. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Real
namespace RosserKernelSharper
open RosserKernelContraction

theorem exp_quarter_le : exp (1/4:ℝ) ≤ 9/7 := by
  have he : exp (1/4:ℝ)^2 = exp (1/2:ℝ) := by
    rw [pow_two, ← exp_add]
    norm_num
  have hp := exp_pos (1/4:ℝ)
  have hb := exp_half_le
  nlinarith

theorem exp_three_quarters_le : exp (3/4:ℝ) ≤ 297/140 := by
  have he : exp (3/4:ℝ) = exp (1/4:ℝ)*exp (1/2:ℝ) := by
    rw [← exp_add]
    norm_num
  rw [he]
  exact (mul_le_mul exp_quarter_le exp_half_le (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem exp_five_quarters_le : exp (5/4:ℝ) ≤ 612/175 := by
  have he : exp (5/4:ℝ) = exp 1*exp (1/4:ℝ) := by
    rw [← exp_add]
    norm_num
  rw [he]
  exact (mul_le_mul exp_one_le exp_quarter_le (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem exp_seven_quarters_le : exp (7/4:ℝ) ≤ 81/14 := by
  have he : exp (7/4:ℝ) = exp (3/2:ℝ)*exp (1/4:ℝ) := by
    rw [← exp_add]
    norm_num
  rw [he]
  exact (mul_le_mul exp_three_halves_le exp_quarter_le (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem log_twelve_fifths_le : log (12/5:ℝ) ≤ 9/10 := by
  apply (log_le_iff_le_exp (by norm_num : (0:ℝ) < 12/5)).mpr
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 9/10) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

theorem log_twelve_sevenths_le : log (12/7:ℝ) ≤ 11/20 := by
  apply (log_le_iff_le_exp (by norm_num : (0:ℝ) < 12/7)).mpr
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 11/20) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

theorem log_four_thirds_le : log (4/3:ℝ) ≤ 3/10 := by
  apply (log_le_iff_le_exp (by norm_num : (0:ℝ) < 4/3)).mpr
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 3/10) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

theorem log_twelve_elevenths_le : log (12/11:ℝ) ≤ 1/11 := by
  have h := log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 12/11)
  linarith

theorem majorant_le (r : ℝ) (hr : 2 ≤ r) : RosserKernelContraction.majorant r ≤ (52/63:ℝ) := by
  unfold RosserKernelContraction.majorant
  split_ifs with hr4
  · by_cases h0 : r ≤ 9/4
    · have hh := interval_bound r (2) (9/4) (9/7) (10/9) (by norm_num)
          hr h0 (by norm_num)
          (by convert exp_quarter_le using 1; norm_num)
          (by convert log_three_le using 1; norm_num)
      exact hh.trans (by norm_num)
    by_cases h1 : r ≤ 5/2
    · have hh := interval_bound r (9/4) (5/2) (33/20) (9/10) (by norm_num)
          (le_of_not_ge h0) h1 (by norm_num)
          (by convert exp_half_le using 1; norm_num)
          (by convert log_twelve_fifths_le using 1; norm_num)
      exact hh.trans (by norm_num)
    by_cases h2 : r ≤ 11/4
    · have hh := interval_bound r (5/2) (11/4) (297/140) (7/10) (by norm_num)
          (le_of_not_ge h1) h2 (by norm_num)
          (by convert exp_three_quarters_le using 1; norm_num)
          (by convert log_two_le using 1; norm_num)
      exact hh.trans (by norm_num)
    by_cases h3 : r ≤ 3
    · have hh := interval_bound r (11/4) (3) (68/25) (11/20) (by norm_num)
          (le_of_not_ge h2) h3 (by norm_num)
          (by convert exp_one_le using 1; norm_num)
          (by convert log_twelve_sevenths_le using 1; norm_num)
      exact hh.trans (by norm_num)
    by_cases h4 : r ≤ 13/4
    · have hh := interval_bound r (3) (13/4) (612/175) (5/12) (by norm_num)
          (le_of_not_ge h3) h4 (by norm_num)
          (by convert exp_five_quarters_le using 1; norm_num)
          (by convert log_three_halves_le using 1; norm_num)
      exact hh.trans (by norm_num)
    by_cases h5 : r ≤ 7/2
    · have hh := interval_bound r (13/4) (7/2) (9/2) (3/10) (by norm_num)
          (le_of_not_ge h4) h5 (by norm_num)
          (by convert exp_three_halves_le using 1; norm_num)
          (by convert log_four_thirds_le using 1; norm_num)
      exact hh.trans (by norm_num)
    by_cases h6 : r ≤ 15/4
    · have hh := interval_bound r (7/2) (15/4) (81/14) (3/16) (by norm_num)
          (le_of_not_ge h5) h6 (by norm_num)
          (by convert exp_seven_quarters_le using 1; norm_num)
          (by convert log_six_fifths_le using 1; norm_num)
      exact hh.trans (by norm_num)
    have hh := interval_bound r (15/4) (4) (15/2) (1/11) (by norm_num)
        (le_of_not_ge h6) hr4 (by norm_num)
        (by convert exp_two_le using 1; norm_num)
        (by convert log_twelve_elevenths_le using 1; norm_num)
    exact hh.trans (by norm_num)
  · have hrp : 0 < r*(r-1) := mul_pos (by linarith) (by linarith)
    apply (div_le_iff₀ hrp).mpr
    have hh := exp_two_le
    have hrr : 12 ≤ r*(r-1) := by nlinarith
    nlinarith

run_cmd do
  for decl in [``exp_quarter_le, ``exp_three_quarters_le, ``exp_five_quarters_le,
    ``exp_seven_quarters_le, ``log_twelve_fifths_le, ``log_twelve_sevenths_le,
    ``log_four_thirds_le, ``log_twelve_elevenths_le, ``majorant_le] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "QUARTER-MESH ROSSER KERNEL MAJORANT AT MOST 52/63 PASSED"
end RosserKernelSharper
end
