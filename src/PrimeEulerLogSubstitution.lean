import PrimeEulerWeightedTransfer
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Exact logarithmic changes of variables for the density appearing in the
actual weighted-prime transfer. The finite integral identity is independent of
the choice of test function, so it also applies to continuous piecewise tests. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real Set MeasureTheory
namespace PrimeEulerLogSubstitution

def parameter (A x : ℝ) : ℝ := A/log x-1

theorem parameter_hasDerivAt (A x : ℝ) (hx : 1 < x) :
    HasDerivAt (parameter A) (-A/(x*(log x)^2)) x := by
  have hx0 : x ≠ 0 := by linarith
  have hl0 : log x ≠ 0 := (Real.log_pos hx).ne'
  convert! (((hasDerivAt_const x A).div (hasDerivAt_log hx0) hl0).sub_const 1) using 1
  field_simp
  ring

theorem parameter_antitoneOn (A a : ℝ) (hA : 0 ≤ A) (ha : 1 < a) :
    AntitoneOn (parameter A) (Ici a) := by
  intro x hx y hy hxy
  unfold parameter
  apply sub_le_sub_right
  exact div_le_div_of_nonneg_left hA (Real.log_pos (ha.trans_le hx))
    (Real.log_le_log (by linarith [hx.out]) hxy)

theorem integral_substitution (F : ℝ → ℝ) (A a b : ℝ) (k : ℕ)
    (hA : 0 < A) (ha : 1 < a) (hab : a ≤ b) :
    (∫ x in a..b, F (parameter A x)/(x*(log x)^(k+2))) =
      (∫ s in parameter A b..parameter A a, F s*(s+1)^k)/A^(k+1) := by
  have hf : ContinuousOn (parameter A) (uIcc a b) := by
    rw [uIcc_of_le hab]
    intro x hx
    exact (parameter_hasDerivAt A x (ha.trans_le hx.1)).continuousAt.continuousWithinAt
  have hd : ∀ x ∈ Ioo (min a b) (max a b),
      HasDerivAt (parameter A) (-A/(x*(log x)^2)) x := by
    simp only [min_eq_left hab, max_eq_right hab]
    intro x hx
    exact parameter_hasDerivAt A x (ha.trans hx.1)
  have hn : ∀ x ∈ Ioo (min a b) (max a b), -A/(x*(log x)^2) ≤ 0 := by
    simp only [min_eq_left hab, max_eq_right hab]
    intro x hx
    exact div_nonpos_of_nonpos_of_nonneg (by linarith)
      (mul_nonneg (by linarith [hx.1]) (sq_nonneg _))
  have hi := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (g := fun s => F s*(s+1)^k) hf hd hn
  have heq : (∫ x in a..b, ((fun s => F s*(s+1)^k) ∘ parameter A) x *
      (-A/(x*(log x)^2))) =
      (∫ x in a..b, -(A^(k+1)) * (F (parameter A x)/(x*(log x)^(k+2)))) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have hl0 : log x ≠ 0 := (Real.log_pos (ha.trans_le hx.1)).ne'
    dsimp [Function.comp_def, parameter]
    rw [sub_add_cancel, div_pow, pow_add, pow_succ]
    field_simp
    ring
  rw [heq, intervalIntegral.integral_const_mul] at hi
  rw [intervalIntegral.integral_symm (a := parameter A b) (b := parameter A a)] at hi
  apply (eq_div_iff (pow_ne_zero _ hA.ne')).mpr
  nlinarith only [hi]

theorem parameter_endpoints (A a b : ℝ) (hA : 0 ≤ A) (ha : 1 < a) (hab : a ≤ b) :
    parameter A b ≤ parameter A a :=
  parameter_antitoneOn A a hA ha (by simp) hab hab

run_cmd do
  for decl in [``parameter_hasDerivAt, ``parameter_antitoneOn,
    ``integral_substitution, ``parameter_endpoints] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end PrimeEulerLogSubstitution
end
