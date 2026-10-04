import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! Explicit exponential-test calculus for a later finite prime-measure
comparison. Every integral here is an ordinary real interval integral; no
arithmetic weighted-transfer estimate is asserted in this module. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Real Set MeasureTheory

namespace PrimeEulerExponentialCalculus

def test (A x : ℝ) : ℝ := exp (1-A/log x)
def moment (A x : ℝ) : ℝ := test A x*(A+log x)/(A^2*log x)
def logKernel (A : ℝ) (k : ℕ) (x : ℝ) : ℝ := test A x/(x*(log x)^k)

theorem test_pos (A x : ℝ) : 0 < test A x := exp_pos _

theorem test_hasDerivAt (A x : ℝ) (hx : 1 < x) :
    HasDerivAt (test A) (test A x*A/(x*(log x)^2)) x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hl0 : log x ≠ 0 := ne_of_gt (log_pos hx)
  have hlog := hasDerivAt_log hx0
  have hh : HasDerivAt (fun y : ℝ => 1-A/log y) (A/(x*(log x)^2)) x := by
    convert! (hasDerivAt_const x (1:ℝ)).sub ((hasDerivAt_const x A).div hlog hl0) using 1
    field_simp
    ring
  convert! hh.exp using 1
  unfold test
  ring

theorem derivative_nonneg (A x : ℝ) (hA : 0 ≤ A) (hx : 1 < x) :
    0 ≤ test A x*A/(x*(log x)^2) := by
  exact div_nonneg (mul_nonneg (test_pos A x).le hA)
    (mul_nonneg (zero_lt_one.trans hx).le (sq_nonneg _))

theorem test_continuousOn (A a b : ℝ) (ha : 1 < a) :
    ContinuousOn (test A) (Icc a b) := by
  intro x hx
  exact (test_hasDerivAt A x (ha.trans_le hx.1)).continuousAt.continuousWithinAt

theorem test_continuousOn_two (A b : ℝ) : ContinuousOn (test A) (Icc 2 b) :=
  test_continuousOn A 2 b (by norm_num)

theorem first_antiderivative_hasDerivAt (A x : ℝ) (hA : 0 < A) (hx : 1 < x) :
    HasDerivAt (fun y => test A y/A) (logKernel A 2 x) x := by
  convert! (test_hasDerivAt A x hx).div_const A using 1
  unfold logKernel
  field_simp

theorem moment_hasDerivAt (A x : ℝ) (hA : 0 < A) (hx : 1 < x) :
    HasDerivAt (moment A) (logKernel A 3 x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hl0 : log x ≠ 0 := ne_of_gt (log_pos hx)
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hlog := hasDerivAt_log hx0
  have hden : A^2*log x ≠ 0 := mul_ne_zero (pow_ne_zero _ hA0) hl0
  convert! ((test_hasDerivAt A x hx).mul ((hasDerivAt_const x A).add hlog)).div
    (hlog.const_mul (A^2)) hden using 1
  dsimp [logKernel]
  field_simp
  ring

theorem moment_nonneg (A x : ℝ) (hA : 0 < A) (hx : 1 < x) :
    0 ≤ moment A x := by
  unfold moment
  exact div_nonneg (mul_nonneg (test_pos A x).le (add_pos hA (log_pos hx)).le)
    (mul_pos (sq_pos_of_pos hA) (log_pos hx)).le

theorem logKernel_nonneg (A x : ℝ) (k : ℕ) (hx : 1 < x) :
    0 ≤ logKernel A k x :=
  div_nonneg (test_pos A x).le
    (mul_nonneg (zero_lt_one.trans hx).le (pow_nonneg (log_pos hx).le _))

theorem logKernel_continuousOn (A a b : ℝ) (k : ℕ) (ha : 1 < a) :
    ContinuousOn (logKernel A k) (Icc a b) := by
  intro x hx
  have hxx : 1 < x := ha.trans_le hx.1
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hxx)
  apply ContinuousAt.continuousWithinAt
  apply (test_hasDerivAt A x hxx).continuousAt.div
    (continuousAt_id.mul ((continuousAt_log hx0).pow k))
  exact ne_of_gt (mul_pos (zero_lt_one.trans hxx) (pow_pos (log_pos hxx) _))

theorem logKernel_intervalIntegrable (A a b : ℝ) (k : ℕ)
    (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (logKernel A k) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact logKernel_continuousOn A a b k (by linarith)

theorem integral_log_sq_eq (A a b : ℝ) (hA : 0 < A) (ha : 2 ≤ a) (hab : a ≤ b) :
    (∫ x in a..b, test A x/(x*(log x)^2)) = test A b/A - test A a/A := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hab] at hx
    exact first_antiderivative_hasDerivAt A x hA (by linarith [hx.1])
  · exact logKernel_intervalIntegrable A a b 2 ha hab

theorem integral_log_cube_eq (A a b : ℝ) (hA : 0 < A) (ha : 2 ≤ a) (hab : a ≤ b) :
    (∫ x in a..b, test A x/(x*(log x)^3)) = moment A b - moment A a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hab] at hx
    exact moment_hasDerivAt A x hA (by linarith [hx.1])
  · exact logKernel_intervalIntegrable A a b 3 ha hab

theorem integral_log_sq_le (A a b : ℝ) (hA : 0 < A) (ha : 2 ≤ a) (hab : a ≤ b) :
    (∫ x in a..b, test A x/(x*(log x)^2)) ≤ test A b/A := by
  rw [integral_log_sq_eq A a b hA ha hab]
  exact sub_le_self _ (div_nonneg (test_pos A a).le hA.le)

theorem integral_log_cube_le (A a b : ℝ) (hA : 0 < A) (ha : 2 ≤ a) (hab : a ≤ b) :
    (∫ x in a..b, test A x/(x*(log x)^3)) ≤ moment A b := by
  rw [integral_log_cube_eq A a b hA ha hab]
  exact sub_le_self _ (moment_nonneg A a hA (by linarith))

run_cmd do
  for decl in [``test_pos, ``test_hasDerivAt, ``derivative_nonneg, ``test_continuousOn,
      ``test_continuousOn_two, ``first_antiderivative_hasDerivAt, ``moment_hasDerivAt,
      ``moment_nonneg, ``logKernel_nonneg, ``logKernel_continuousOn,
      ``logKernel_intervalIntegrable, ``integral_log_sq_eq, ``integral_log_cube_eq,
      ``integral_log_sq_le, ``integral_log_cube_le] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "PRIME EULER EXPONENTIAL TEST CALCULUS: STANDARD AXIOMS ONLY"

end PrimeEulerExponentialCalculus
end
