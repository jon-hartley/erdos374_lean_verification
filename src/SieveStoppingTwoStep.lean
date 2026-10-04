import SieveStoppingRecurrence
import SieveEulerRatio

/-! Exact two-step equation for the actual normalized lower stopping loss.
The forcing records a closed second gate, while the operator records an open
second gate and evaluates the loss at the smaller prime pool. No decay estimate
or continuous comparison is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SieveStoppingTwoStep
open SieveStoppingExpansion SieveStoppingRecurrence

def normalizedLower (T z : ℝ) : ℝ := lowerLoss T z / primeEuler z

def forcing (T z : ℝ) : ℝ :=
  ∑ p ∈ SieveSmallWeights.pool z, ∑ q ∈ SieveSmallWeights.pool (p:ℝ),
    if (q:ℝ)^3 < T/(p:ℝ) then 0
    else (p:ℝ)⁻¹ * (q:ℝ)⁻¹ * primeEuler (q:ℝ) / primeEuler z

def operator (f : ℝ → ℝ → ℝ) (T z : ℝ) : ℝ :=
  ∑ p ∈ SieveSmallWeights.pool z, ∑ q ∈ SieveSmallWeights.pool (p:ℝ),
    if (q:ℝ)^3 < T/(p:ℝ) then
      (p:ℝ)⁻¹ * (q:ℝ)⁻¹ * primeEuler (q:ℝ) / primeEuler z *
        f ((T/(p:ℝ))/(q:ℝ)) (q:ℝ)
    else 0

theorem normalizedLower_nonneg (T z : ℝ) : 0 ≤ normalizedLower T z := by
  apply div_nonneg _ (SieveEulerRatio.euler_pos z).le
  exact (SieveReciprocalModel.loss_nonnegative (SieveRosser.cubicGate T) 1
    (SieveSmallWeights.primes z) (SieveSmallWeights.primes_nodup z)
    (SieveSmallWeights.primes_prime z)).1

theorem forcing_nonneg (T z : ℝ) : 0 ≤ forcing T z := by
  unfold forcing
  apply Finset.sum_nonneg
  intro p hp
  apply Finset.sum_nonneg
  intro q hq
  split_ifs
  · exact le_rfl
  · exact div_nonneg (mul_nonneg
      (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p))
        (inv_nonneg.mpr (Nat.cast_nonneg q)))
      (SieveEulerRatio.euler_pos (q:ℝ)).le)
      (SieveEulerRatio.euler_pos z).le

theorem operator_nonneg (f : ℝ → ℝ → ℝ)
    (hf : ∀ T z, 0 ≤ f T z) (T z : ℝ) : 0 ≤ operator f T z := by
  unfold operator
  apply Finset.sum_nonneg
  intro p hp
  apply Finset.sum_nonneg
  intro q hq
  split_ifs
  · exact mul_nonneg (div_nonneg (mul_nonneg
      (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p))
        (inv_nonneg.mpr (Nat.cast_nonneg q)))
      (SieveEulerRatio.euler_pos (q:ℝ)).le)
      (SieveEulerRatio.euler_pos z).le) (hf _ _)
  · exact le_rfl

theorem normalizedLower_two_step (T z : ℝ) :
    normalizedLower T z = forcing T z + operator normalizedLower T z := by
  have cancel (a b c d : ℝ) (hb : b ≠ 0) (hc : c ≠ 0) :
      a * b / c * (d / b) = a * d / c := by
    field_simp
  unfold normalizedLower forcing operator
  rw [lowerLoss_first_prime, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [upperLoss_first_prime, Finset.mul_sum, Finset.sum_div,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  split_ifs with hgate
  · simp only [zero_add]
    rw [cancel _ _ _ _ (ne_of_gt (SieveEulerRatio.euler_pos (q:ℝ)))
      (ne_of_gt (SieveEulerRatio.euler_pos z))]
    ring
  · simp only [add_zero]
    ring

run_cmd do
  for decl in [``normalizedLower, ``forcing, ``operator,
      ``normalizedLower_nonneg, ``forcing_nonneg, ``operator_nonneg,
      ``normalizedLower_two_step] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL NORMALIZED TWO-STEP EQUATION AND NONNEGATIVITY PASSED; NO DECAY CLAIM"

end SieveStoppingTwoStep
end
