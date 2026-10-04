import SieveEulerRatio
import SieveCollisionBounds

/-! Exact finite prime Euler logarithms with a uniformly summable quadratic error. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
namespace PrimeEulerLogBounds
open SieveStoppingExpansion

def intervalPrimes (a b : ℝ) : Finset ℕ := SieveBoxedFamily.pool a 1 b
def reciprocalMass (a b : ℝ) : ℝ := ∑ p ∈ intervalPrimes a b, (p : ℝ)⁻¹
def logError (a b : ℝ) : ℝ :=
  Real.log (primeEuler a / primeEuler b) - reciprocalMass a b

theorem mem_intervalPrimes (a b : ℝ) (p : ℕ) :
    p ∈ intervalPrimes a b ↔ p.Prime ∧ (p : ℝ) < b ∧ a ≤ (p : ℝ) := by
  simpa only [intervalPrimes, one_pow, Real.rpow_one] using SieveBoxedFamily.mem_pool a 1 b p

theorem ratio_eq_product (a b : ℝ) (hab : a ≤ b) :
    primeEuler a / primeEuler b = ∏ p ∈ intervalPrimes a b, 1/(1-(p : ℝ)⁻¹) := by
  simpa only [one_pow, Real.rpow_one, intervalPrimes] using
    SieveEulerRatio.ratio_eq_product_inverse a 1 b (by simpa using hab)

theorem neg_log_one_sub_bounds (w : ℝ) (_hw : 0 ≤ w) (hw2 : w ≤ 1/2) :
    0 ≤ -Real.log (1-w)-w ∧ -Real.log (1-w)-w ≤ 2*w^2 := by
  have hp : 0 < 1-w := by linarith
  have hl := Real.log_le_sub_one_of_pos hp
  have hu := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [Real.log_inv] at hu
  have hr : (1-w)⁻¹ ≤ 1+w+2*w^2 := by
    rw [← one_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith [mul_nonneg (sq_nonneg w) (show 0 ≤ 1-2*w by linarith)]
  exact ⟨by linarith, by linarith⟩

theorem log_ratio_eq_sum (a b : ℝ) (hab : a ≤ b) :
    Real.log (primeEuler a / primeEuler b) =
      ∑ p ∈ intervalPrimes a b, -Real.log (1-(p : ℝ)⁻¹) := by
  rw [ratio_eq_product a b hab, Real.log_prod]
  · simp only [one_div, Real.log_inv]
  · intro p hp
    apply one_div_ne_zero
    apply ne_of_gt
    apply sub_pos.mpr
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast ((mem_intervalPrimes a b p).mp hp).1.one_lt

theorem logError_bounds (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    0 ≤ logError a b ∧ logError a b ≤ 2/(a-1) := by
  have ht : ∀ p ∈ intervalPrimes a b,
      0 ≤ -Real.log (1-(p : ℝ)⁻¹)-(p : ℝ)⁻¹ ∧
        -Real.log (1-(p : ℝ)⁻¹)-(p : ℝ)⁻¹ ≤ 2*((p : ℝ)^2)⁻¹ := by
    intro p hp
    have hpa := ((mem_intervalPrimes a b p).mp hp).2.2
    have hi : (p : ℝ)⁻¹ ≤ 1/2 := by
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
        (ha.trans hpa)
    simpa only [inv_pow] using neg_log_one_sub_bounds (p : ℝ)⁻¹ (by positivity) hi
  unfold logError reciprocalMass
  rw [log_ratio_eq_sum a b hab, ← Finset.sum_sub_distrib]
  constructor
  · exact Finset.sum_nonneg (fun p hp => (ht p hp).1)
  · calc
      _ ≤ ∑ p ∈ intervalPrimes a b, 2*((p : ℝ)^2)⁻¹ :=
        Finset.sum_le_sum (fun p hp => (ht p hp).2)
      _ = 2 * SieveCollisionBounds.diagonalMass (intervalPrimes a b) := by
        rw [SieveCollisionBounds.diagonalMass, Finset.mul_sum]
      _ ≤ 2 * (1/(a-1)) := mul_le_mul_of_nonneg_left
        (SieveCollisionBounds.diagonalMass_le _ a (by linarith)
          (fun p hp => ((mem_intervalPrimes a b p).mp hp).2.2)) (by norm_num)
      _ = _ := by ring

theorem log_ratio_le_reciprocal_add (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    Real.log (primeEuler a / primeEuler b) ≤ reciprocalMass a b + 2/(a-1) := by
  have h := (logError_bounds a b ha hab).2
  unfold logError at h
  linarith

/-- The nonlinear Euler error is also bounded on the reciprocal-log scale. -/
theorem log_ratio_le_reciprocal_add_log (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    Real.log (primeEuler a / primeEuler b) ≤ reciprocalMass a b + 2/Real.log a := by
  apply (log_ratio_le_reciprocal_add a b ha hab).trans
  apply add_le_add le_rfl
  exact div_le_div_of_nonneg_left (by norm_num) (Real.log_pos (by linarith))
    (Real.log_le_sub_one_of_pos (by linarith))

/-- A linear majorant for an exponential on a fixed bounded interval. -/
theorem exp_le_one_add_mul_exp_bound (t T : ℝ) (ht : 0 ≤ t) (hT : t ≤ T) :
    Real.exp t ≤ 1 + t * Real.exp T := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-t)) (Real.exp_pos t).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  have hh : t * Real.exp t ≤ t * Real.exp T :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hT) ht
  nlinarith

#print axioms logError_bounds
run_cmd do
  for decl in [``mem_intervalPrimes, ``ratio_eq_product, ``neg_log_one_sub_bounds,
    ``log_ratio_eq_sum, ``logError_bounds, ``log_ratio_le_reciprocal_add,
    ``log_ratio_le_reciprocal_add_log, ``exp_le_one_add_mul_exp_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end PrimeEulerLogBounds
end
