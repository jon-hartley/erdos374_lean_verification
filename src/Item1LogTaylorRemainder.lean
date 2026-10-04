import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! Arbitrary-degree logarithmic Taylor polynomials with an explicit remainder.
The estimates here are scalar identities and inequalities. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators

namespace Item1LogTaylorRemainder

/-- The first d terms of the Taylor polynomial for log(1+x). -/
def logPolynomial (d : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range d, (-1 : ℝ)^k * x^(k+1) / (k+1)

theorem negative_power_sum (d : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range d, (-x)^(k+1) / (k+1)) = -logPolynomial d x := by
  rw [logPolynomial, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hp : (-x)^(k+1) = -((-1 : ℝ)^k * x^(k+1)) := by
    calc
      (-x)^(k+1) = ((-1 : ℝ)*x)^(k+1) := by congr 1; ring
      _ = -((-1 : ℝ)^k * x^(k+1)) := by
        rw [mul_pow, pow_succ (-1 : ℝ)]
        ring
  rw [hp, neg_div]

/-- A geometric remainder valid on the full open unit interval. -/
theorem log_taylor_error_le_geometric (d : ℕ) (x : ℝ) (hx : |x| < 1) :
    |Real.log (1+x) - logPolynomial d x| ≤ |x|^(d+1) / (1-|x|) := by
  have hh := Real.abs_log_sub_add_sum_range_le (x := -x)
    (by simpa only [abs_neg] using hx) d
  rw [negative_power_sum] at hh
  simpa only [abs_neg, sub_neg_eq_add, sub_eq_add_neg, neg_neg, add_comm] using hh

/-- A uniform, arbitrary-degree estimate on 0 ≤ x ≤ 1/2. -/
theorem log_taylor_error_le (d : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hhalf : x ≤ 1/2) :
    |Real.log (1+x) - logPolynomial d x| ≤ 2*x^(d+1) := by
  have hx1 : |x| < 1 := by rw [abs_of_nonneg hx]; linarith only [hhalf]
  have hh := log_taylor_error_le_geometric d x hx1
  rw [abs_of_nonneg hx] at hh
  have hden : 0 < 1-x := by linarith only [hhalf]
  apply hh.trans
  apply (div_le_iff₀ hden).mpr
  have hm := mul_le_mul_of_nonneg_left hhalf (pow_nonneg hx (d+1))
  nlinarith only [hm]

/-- Expansion of log(y+h)-log y, with degree independent of y and h. -/
theorem shifted_log_taylor_error_le (d : ℕ) (y h : ℝ) (hy : 0 < y)
    (hh : 0 ≤ h) (hhalf : h ≤ y/2) :
    |Real.log (y+h) - (Real.log y + logPolynomial d (h/y))| ≤
      2*(h/y)^(d+1) := by
  have hx : 0 ≤ h/y := div_nonneg hh hy.le
  have hxhalf : h/y ≤ 1/2 := by
    apply (div_le_iff₀ hy).mpr
    linarith only [hhalf]
  have hidentity : Real.log (y+h) - Real.log y = Real.log (1+h/y) := by
    rw [← Real.log_div (by linarith only [hy,hh] : y+h ≠ 0) hy.ne']
    congr 1
    field_simp
  rw [sub_add_eq_sub_sub, hidentity]
  exact log_taylor_error_le d (h/y) hx hxhalf

end Item1LogTaylorRemainder

run_cmd do
  for target in [``Item1LogTaylorRemainder.negative_power_sum,
      ``Item1LogTaylorRemainder.log_taylor_error_le_geometric,
      ``Item1LogTaylorRemainder.log_taylor_error_le,
      ``Item1LogTaylorRemainder.shifted_log_taylor_error_le] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1LogTaylorRemainder: 4 theorem guards passed."
