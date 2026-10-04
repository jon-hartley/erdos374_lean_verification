import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Log.Sum
import Mathlib.Tactic

/-! An elementary first Mertens estimate for the actual Mangoldt reciprocal
sum.  The proof uses only the exact divisor identity, factorial/logarithm
sums, and Mathlib's unconditional Chebyshev upper bound. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace MangoldtReciprocal

def coefficient (n : ℕ) : ℝ := Λ n / n
def mass (x : ℝ) : ℝ := ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, coefficient n

theorem coefficient_nonneg (n : ℕ) : 0 ≤ coefficient n := by
  unfold coefficient
  positivity

theorem sum_coefficient_Icc (x : ℝ) :
    ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, coefficient n = mass x := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
  simp [coefficient, mass]

theorem sum_log_eq_mangoldt_floor (x : ℝ) :
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Real.log n =
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n * (⌊x / n⌋₊ : ℝ) := by
  simpa only [ArithmeticFunction.vonMangoldt_mul_zeta, ArithmeticFunction.log_apply,
    Nat.floor_div_natCast] using
      ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum ArithmeticFunction.vonMangoldt ⌊x⌋₊

theorem mul_mass_eq (x : ℝ) :
    x * mass x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n * (x / n) := by
  simp only [mass, coefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem sum_log_le_mul_mass (x : ℝ) (hx : 0 ≤ x) :
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Real.log n ≤ x * mass x := by
  rw [sum_log_eq_mangoldt_floor, mul_mass_eq]
  apply Finset.sum_le_sum
  intro n _
  exact mul_le_mul_of_nonneg_left
    (Nat.floor_le (div_nonneg hx (Nat.cast_nonneg _))) ArithmeticFunction.vonMangoldt_nonneg

theorem mul_mass_le_sum_log_add_psi (x : ℝ) :
    x * mass x ≤ (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Real.log n) + Chebyshev.psi x := by
  rw [sum_log_eq_mangoldt_floor, Chebyshev.psi, mul_mass_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n _
  have h := mul_le_mul_of_nonneg_left (Nat.lt_floor_add_one (x / n)).le
    (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  simpa only [mul_add, mul_one] using h

/-- A global leading-coefficient-one estimate, with explicit bounded error. -/
theorem mass_bounds (x : ℝ) (hx : 1 ≤ x) :
    Real.log x - 2 ≤ mass x ∧ mass x ≤ Real.log x + 7 := by
  have hx0 : 0 < x := by linarith
  have hloglower := Real.le_sum_log' hx
  have hlogupper := Real.sum_log_le' hx
  have hfloorlower := sum_log_le_mul_mass x hx0.le
  have hfloorupper := mul_mass_le_sum_log_add_psi x
  have hpsi := Chebyshev.psi_le_const_mul_self hx0.le
  have hfour : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  constructor
  · apply (mul_le_mul_iff_right₀ hx0).mp
    nlinarith
  · apply (mul_le_mul_iff_right₀ hx0).mp
    nlinarith

theorem abs_mass_sub_log_le (x : ℝ) (hx : 1 ≤ x) :
    |mass x - Real.log x| ≤ 7 := by
  obtain ⟨hl, hu⟩ := mass_bounds x hx
  exact abs_le.mpr ⟨by linarith, by linarith⟩

#print axioms mass_bounds
run_cmd do
  for decl in [``coefficient_nonneg, ``sum_coefficient_Icc, ``sum_log_eq_mangoldt_floor,
    ``mul_mass_eq, ``sum_log_le_mul_mass, ``mul_mass_le_sum_log_add_psi,
    ``mass_bounds, ``abs_mass_sub_log_le] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end MangoldtReciprocal
end
