import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! A certified numerical contraction majorant for the dimension-one,
two-step continuous Rosser tail operator. This is a scalar estimate only;
the integral comparison and the arithmetic transfer are separate results. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators

namespace RosserKernelContraction

def majorant (r : ℝ) : ℝ :=
  if r ≤ 4 then Real.exp (r-2)/r*(Real.log (3/(r-1))+1/3)
  else Real.exp 2/(r*(r-1))

theorem exp_one_le : Real.exp 1 ≤ (68/25:ℝ) := by
  exact Real.exp_one_lt_d9.le.trans (by norm_num)

theorem exp_half_le : Real.exp (1/2:ℝ) ≤ 33/20 := by
  have hh : Real.exp (1/2:ℝ)^2 = Real.exp 1 := by
    rw [pow_two, ← Real.exp_add]
    norm_num
  have hp := Real.exp_pos (1/2:ℝ)
  have hb := exp_one_le
  nlinarith

theorem exp_three_halves_le : Real.exp (3/2:ℝ) ≤ 9/2 := by
  have heq : Real.exp (3/2:ℝ) = Real.exp 1 * Real.exp (1/2:ℝ) := by
    rw [← Real.exp_add]
    norm_num
  rw [heq]
  have hh := mul_le_mul exp_one_le exp_half_le (Real.exp_pos _).le (by norm_num : (0:ℝ) ≤ 68/25)
  exact hh.trans (by norm_num)

theorem exp_two_le : Real.exp 2 ≤ (15/2:ℝ) := by
  have heq : Real.exp (2:ℝ) = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [heq]
  have hh := mul_le_mul exp_one_le exp_one_le (Real.exp_pos _).le (by norm_num : (0:ℝ) ≤ 68/25)
  exact hh.trans (by norm_num)

theorem log_three_le : Real.log 3 ≤ (10/9:ℝ) := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0:ℝ)<3)).mpr
  have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 10/9) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at hh ⊢
  linarith

theorem log_two_le : Real.log 2 ≤ (7/10:ℝ) := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0:ℝ)<2)).mpr
  have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 7/10) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at hh ⊢
  linarith

theorem log_three_halves_le : Real.log (3/2:ℝ) ≤ 5/12 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0:ℝ)<3/2)).mpr
  have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 5/12) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at hh ⊢
  linarith

theorem log_six_fifths_le : Real.log (6/5:ℝ) ≤ 3/16 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0:ℝ)<6/5)).mpr
  have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 3/16) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at hh ⊢
  linarith

theorem exp_div_mono (x y : ℝ) (hx : 1 ≤ x) (hxy : x ≤ y) :
    Real.exp (x-2)/x ≤ Real.exp (y-2)/y := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hypos : 0 < y := hxpos.trans_le hxy
  have hlin : y ≤ x*(1+(y-x)) := by nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hxy)]
  have hexp : 1+(y-x) ≤ Real.exp (y-x) := by
    simpa only [add_comm] using Real.add_one_le_exp (y-x)
  have hmul : y ≤ x*Real.exp (y-x) :=
    hlin.trans (mul_le_mul_of_nonneg_left hexp hxpos.le)
  have heq : Real.exp (y-2) = Real.exp (x-2)*Real.exp (y-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  apply (div_le_div_iff₀ hxpos hypos).mpr
  rw [heq]
  nlinarith only [mul_le_mul_of_nonneg_left hmul (Real.exp_pos (x-2)).le]

theorem interval_bound (r a b E L : ℝ) (ha : 2 ≤ a)
    (hra : a ≤ r) (hrb : r ≤ b) (hb : b ≤ 4)
    (hE : Real.exp (b-2) ≤ E) (hL : Real.log (3/(a-1)) ≤ L) :
    Real.exp (r-2)/r*(Real.log (3/(r-1))+1/3) ≤ (E/b)*(L+1/3) := by
  have hrpos : 0 < r := by linarith
  have hbpos : 0 < b := by linarith
  have hra1 : 0 < r-1 := by linarith
  have ha1 : 0 < a-1 := by linarith
  have hquot : (3:ℝ)/(r-1) ≤ 3/(a-1) :=
    div_le_div_of_nonneg_left (by norm_num) ha1 (by linarith)
  have hlog : Real.log (3/(r-1)) ≤ L :=
    (Real.log_le_log (div_pos (by norm_num) hra1) hquot).trans hL
  have hratio : (1:ℝ) ≤ 3/(r-1) := (le_div_iff₀ hra1).mpr (by linarith)
  have hnonneg : 0 ≤ Real.log (3/(r-1))+1/3 := by
    have hh := Real.log_nonneg hratio
    linarith
  have hfirst : Real.exp (r-2)/r ≤ E/b :=
    (exp_div_mono r b (by linarith) hrb).trans
      (div_le_div_of_nonneg_right hE hbpos.le)
  have hEpos : 0 ≤ E/b :=
    div_nonneg ((Real.exp_pos _).le.trans hE) hbpos.le
  exact mul_le_mul hfirst (by linarith) hnonneg hEpos

theorem majorant_le (r : ℝ) (hr : 2 ≤ r) : majorant r ≤ (99/100:ℝ) := by
  unfold majorant
  split_ifs with hr4
  · by_cases h1 : r ≤ 5/2
    · have hh := interval_bound r 2 (5/2) (33/20) (10/9) (by norm_num) hr h1
        (by norm_num) (by convert exp_half_le using 1; norm_num)
        (by convert log_three_le using 1; norm_num)
      exact hh.trans (by norm_num)
    · by_cases h2 : r ≤ 3
      · have hh := interval_bound r (5/2) 3 (11/4) (7/10) (by norm_num)
          (le_of_not_ge h1) h2 (by norm_num)
          (by convert exp_one_le.trans (by norm_num : (68/25:ℝ) ≤ 11/4) using 1; norm_num)
          (by convert log_two_le using 1; norm_num)
        exact hh.trans (by norm_num)
      · by_cases h3 : r ≤ 7/2
        · have hh := interval_bound r 3 (7/2) (9/2) (5/12) (by norm_num)
            (le_of_not_ge h2) h3 (by norm_num)
            (by convert exp_three_halves_le using 1; norm_num)
            (by convert log_three_halves_le using 1; norm_num)
          exact hh.trans (by norm_num)
        · have hh := interval_bound r (7/2) 4 (15/2) (3/16) (by norm_num)
            (le_of_not_ge h3) hr4 (by norm_num)
            (by convert exp_two_le using 1; norm_num)
            (by convert log_six_fifths_le using 1; norm_num)
          exact hh.trans (by norm_num)
  · have hrp : 0 < r*(r-1) := mul_pos (by linarith) (by linarith)
    apply (div_le_iff₀ hrp).mpr
    have hh := exp_two_le
    have hrr : 12 ≤ r*(r-1) := by nlinarith
    nlinarith

theorem majorant_lt_one (r : ℝ) (hr : 2 ≤ r) : majorant r < 1 :=
  (majorant_le r hr).trans_lt (by norm_num)

run_cmd do
  for decl in [``exp_one_le, ``exp_half_le, ``exp_three_halves_le, ``exp_two_le,
      ``log_three_le, ``log_two_le, ``log_three_halves_le, ``log_six_fifths_le,
      ``exp_div_mono, ``interval_bound, ``majorant_le, ``majorant_lt_one] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ROSSER KERNEL SCALAR CONTRACTION: STANDARD AXIOMS ONLY"

end RosserKernelContraction
end
