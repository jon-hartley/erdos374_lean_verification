import CancellationDilation
import PositiveSharpRemainderRegularity

/-! Unconditional signed first moments of actual physical divisor remainders.
The absolute value is outside the integral: no absolute first moment or
second moment is claimed by these results. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace CancellationDivisorBias
open CancellationDilation

theorem centeredFloor_scaled_integrable (d : ℕ) (a b α : ℝ) (hα : α≠0) :
    IntervalIntegrable (fun x => centeredFloor d (α*x)) volume a b := by
  have hh := (centeredFloor_integrable d (α*a) (α*b)).comp_mul_left (c:=α)
  simpa only [mul_div_cancel_left₀ _ hα] using hh

theorem divisor_interval_bias (d : ℕ) (X α : ℝ) (hX : 0≤X) (hα : 0<α) (hα1 : α≤1) :
    |∫x in X..2*X,
      ((⌊x/d⌋₊:ℝ)-(⌊α*x/d⌋₊:ℝ)-(x-α*x)/d)|≤2*(1-α)*X := by
  have hh := dilation_bias (centeredFloor d) (1/2) X α hX hα hα1
    (centeredFloor_integrable d) (centeredFloor_bound d)
  have hi := centeredFloor_integrable d X (2*X)
  have hs := centeredFloor_scaled_integrable d X (2*X) α hα.ne'
  simp_rw [←centeredFloor_difference]
  rw [intervalIntegral.integral_sub hi hs,
    intervalIntegral.integral_comp_mul_left _ hα.ne', smul_eq_mul]
  convert hh using 1; ring

theorem divisor_set_integrable (d : ℕ) (X α : ℝ) (hX : 0≤X) (hα : α≠0) :
    IntegrableOn (fun x:ℝ => (⌊x/d⌋₊:ℝ)-(⌊α*x/d⌋₊:ℝ)-(x-α*x)/d)
      (Icc X (2*X)) := by
  rw [←intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : X≤2*X)]
  simp_rw [←centeredFloor_difference]
  exact (centeredFloor_integrable d X (2*X)).sub
    (centeredFloor_scaled_integrable d X (2*X) α hα)

theorem divisor_set_bias (d : ℕ) (X α : ℝ) (hX : 0≤X) (hα : 0<α) (hα1 : α≤1) :
    |∫x in Icc X (2*X),
      ((⌊x/d⌋₊:ℝ)-(⌊α*x/d⌋₊:ℝ)-(x-α*x)/d)|≤2*(1-α)*X := by
  rw [integral_Icc_eq_integral_Ioc, ←intervalIntegral.integral_of_le (by linarith : X≤2*X)]
  exact divisor_interval_bias d X α hX hα hα1

theorem remainder_integral_identity (S : Finset ℕ) (w : ℕ→ℝ) (X α : ℝ)
    (hX : 0≤X) (hα : α≠0) :
    (∫x in Icc X (2*X), HarmanDivisorWindow.remainder S w (α*x) x) =
      ∑d∈S, w d*(∫x in Icc X (2*X),
        ((⌊x/d⌋₊:ℝ)-(⌊α*x/d⌋₊:ℝ)-(x-α*x)/d)) := by
  simp_rw [HarmanDivisorWindow.remainder_eq_sum]
  rw [integral_finsetSum _ (fun d _ => (divisor_set_integrable d X α hX hα).const_mul _)]
  exact Finset.sum_congr rfl (fun d _ => integral_const_mul _ _)

theorem remainder_integral_bias (S : Finset ℕ) (w : ℕ→ℝ) (X α : ℝ)
    (hX : 0≤X) (hα : 0<α) (hα1 : α≤1) :
    |∫x in Icc X (2*X), HarmanDivisorWindow.remainder S w (α*x) x|≤
      2*(1-α)*X*(∑d∈S, |w d|) := by
  rw [remainder_integral_identity S w X α hX hα.ne']
  calc
    _ ≤ ∑d∈S, |w d*(∫x in Icc X (2*X),
        ((⌊x/d⌋₊:ℝ)-(⌊α*x/d⌋₊:ℝ)-(x-α*x)/d))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑d∈S, |w d| * (2*(1-α)*X) := by
      apply Finset.sum_le_sum
      intro d _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (divisor_set_bias d X α hX hα hα1) (abs_nonneg _)
    _ = _ := by rw [←Finset.sum_mul]; ring

theorem moving_remainder_integral_bias (S : Finset ℕ) (w : ℕ→ℝ) (X Y : ℝ)
    (hX : 0<X) (hY : 0≤Y) (hYX : Y<X) :
    |∫x in Icc X (2*X), HarmanDivisorWindow.remainder S w (x-x*Y/X) x|≤
      2*Y*(∑d∈S, |w d|) := by
  have hα : 0<1-Y/X := by have hh := (div_lt_one hX).mpr hYX; linarith
  have hα1 : 1-Y/X≤1 := by linarith [div_nonneg hY hX.le]
  have hh := remainder_integral_bias S w X (1-Y/X) hX.le hα hα1
  have he : (fun x:ℝ => (1-Y/X)*x) = (fun x => x-x*Y/X) := by funext x; ring
  simp_rw [congrFun he] at hh
  convert hh using 1
  field_simp
  ring

run_cmd do
  for decl in [``centeredFloor_scaled_integrable, ``divisor_interval_bias,
      ``divisor_set_integrable, ``divisor_set_bias, ``remainder_integral_identity,
      ``remainder_integral_bias, ``moving_remainder_integral_bias] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "SIGNED FIRST MOMENTS OF PHYSICAL DIVISOR REMAINDERS PASSED"

end CancellationDivisorBias
