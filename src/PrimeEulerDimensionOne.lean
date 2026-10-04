import PrimeEulerLogBounds
import MertensPrimeInterval

/-! An unconditional dimension-one Euler-product comparison for the actual primes.
The explicit constant is intentionally coarse and independent of both endpoints. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
namespace PrimeEulerDimensionOne
open PrimeEulerLogBounds SieveStoppingExpansion

def errorConstant : ℝ := 12 * Real.exp (12 / Real.log 2)

theorem errorConstant_pos : 0 < errorConstant := by
  unfold errorConstant
  positivity

theorem reciprocalMass_le (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    reciprocalMass a b ≤ Real.log (Real.log b / Real.log a) + 10 / Real.log a := by
  exact MertensPrimeInterval.prime_reciprocal_interval a b (intervalPrimes a b)
    (by linarith) hab (fun p hp => by
      have h := (mem_intervalPrimes a b p).mp hp
      exact ⟨h.1, h.2.2, h.2.1.le⟩)

theorem log_ratio_bound (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    Real.log (primeEuler a / primeEuler b) ≤
      Real.log (Real.log b / Real.log a) + 12 / Real.log a := by
  have h := log_ratio_le_reciprocal_add_log a b ha hab
  have hm := reciprocalMass_le a b ha hab
  simp only [div_eq_mul_inv] at h hm ⊢
  linarith

theorem ratio_bound_exp (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    primeEuler a / primeEuler b ≤
      (Real.log b / Real.log a) * Real.exp (12 / Real.log a) := by
  have hla : 0 < Real.log a := Real.log_pos (by linarith)
  have hlb : 0 < Real.log b := Real.log_pos (by linarith)
  have hp : 0 < primeEuler a / primeEuler b :=
    div_pos (SieveEulerRatio.euler_pos a) (SieveEulerRatio.euler_pos b)
  calc
    _ = Real.exp (Real.log (primeEuler a / primeEuler b)) := (Real.exp_log hp).symm
    _ ≤ Real.exp (Real.log (Real.log b / Real.log a) + 12 / Real.log a) :=
      Real.exp_le_exp.mpr (log_ratio_bound a b ha hab)
    _ = _ := by rw [Real.exp_add, Real.exp_log (div_pos hlb hla)]

/-- The source's dimension-one prime/Euler condition, with a single absolute
constant and no remaining prime-distribution premise or eventual threshold. -/
theorem ratio_bound (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    primeEuler a / primeEuler b ≤
      (Real.log b / Real.log a) * (1 + errorConstant / Real.log a) := by
  have hla : 0 < Real.log a := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsmall : 12 / Real.log a ≤ 12 / Real.log 2 :=
    div_le_div_of_nonneg_left (by norm_num) hl2
      (Real.log_le_log (by norm_num) ha)
  have he := exp_le_one_add_mul_exp_bound (12 / Real.log a) (12 / Real.log 2)
    (div_nonneg (by norm_num) hla.le) hsmall
  have he' : Real.exp (12 / Real.log a) ≤ 1 + errorConstant / Real.log a := by
    convert he using 1
    unfold errorConstant
    ring
  exact (ratio_bound_exp a b ha hab).trans
    (mul_le_mul_of_nonneg_left he' (div_nonneg (Real.log_pos (by linarith)).le hla.le))

theorem product_bound (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    (∏ p ∈ intervalPrimes a b, 1/(1-(p : ℝ)⁻¹)) ≤
      (Real.log b / Real.log a) * (1 + errorConstant / Real.log a) := by
  rw [← ratio_eq_product a b hab]
  exact ratio_bound a b ha hab

theorem actual_grid_ratio (D s z : ℝ) (hu : 2 ≤ D^(s^2)) (huz : D^(s^2) ≤ z) :
    primeEuler (D^(s^2)) / primeEuler z ≤
      (Real.log z / Real.log (D^(s^2))) * (1 + errorConstant / Real.log (D^(s^2))) :=
  ratio_bound _ z hu huz

#print axioms ratio_bound
run_cmd do
  for decl in [``errorConstant_pos, ``reciprocalMass_le, ``log_ratio_bound,
    ``ratio_bound_exp, ``ratio_bound, ``product_bound, ``actual_grid_ratio] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end PrimeEulerDimensionOne
end
