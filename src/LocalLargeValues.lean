import DirichletLargeValues

/-!
Absorption of the proved Gram-kernel error on a short frequency block.
E is an explicit upper bound for the squared coefficient energy.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators

namespace LocalLargeValues
open Erdos374.HarmanAnalytic151MeanSquare

theorem count_bound (N lo hi : ℕ) (coeff : ℕ → ℂ) (r : Finset ℝ)
    (T H E V : ℝ) (hN : 1 ≤ N) (hlo : N ≤ lo) (hhi : hi ≤ 2 * N)
    (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) (hV : 0 < V)
    (henergy : (∑ n ∈ Finset.Ioc lo hi, ‖coeff n‖ ^ 2) ≤ E)
    (hsep : ∀ x ∈ r, ∀ y ∈ r, x ≠ y → 1 ≤ |x - y|)
    (hdiamT : ∀ x ∈ r, ∀ y ∈ r, |x - y| ≤ T)
    (hdiamH : ∀ x ∈ r, ∀ y ∈ r, |x - y| ≤ H)
    (hlarge : ∀ t ∈ r, V ≤ ‖exponentialSum151 (Finset.Ioc lo hi)
      coeff (fun n => Real.log n) t‖)
    (habsorb : 1024 * E * Real.sqrt (H * (1 + Real.log ((N : ℝ) + 1))) ≤ V ^ 2) :
    (r.card : ℝ) ≤ 258 * N * (1 + Real.log (T + 1)) * E / V ^ 2 := by
  have hmin : 0 ≤ min T H := le_min hT hH
  have hlog : 0 ≤ Real.log (min T H + 1) := Real.log_nonneg (by linarith)
  have hG : 0 ≤ 1 + Real.log ((N : ℝ) + 1) := by
    have hh := Real.log_nonneg (show 1 ≤ (N : ℝ) + 1 by
      linarith [Nat.cast_nonneg (α := ℝ) N])
    linarith
  have hbase := DirichletLargeValues.large_value_energy N lo hi coeff r (min T H) V
    hN hlo hhi hmin hV.le hsep
    (fun x hx y hy => le_min (hdiamT x hx y hy) (hdiamH x hx y hy)) hlarge
  have hreplace := mul_le_mul_of_nonneg_left henergy
    (show 0 ≤ 129 * N * (1 + Real.log (min T H + 1)) +
      512 * r.card * Real.sqrt (min T H * (1 + Real.log ((N : ℝ) + 1))) by positivity)
  have hlogLe : 1 + Real.log (min T H + 1) ≤ 1 + Real.log (T + 1) := by
    have hh := Real.log_le_log (by linarith : 0 < min T H + 1)
      (show min T H + 1 ≤ T + 1 by linarith [min_le_left T H])
    linarith
  have hsqrt := Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_right (min_le_right T H) hG)
  have hcoeff := add_le_add
    (mul_le_mul_of_nonneg_left hlogLe (show 0 ≤ 129 * (N : ℝ) by positivity))
    (mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ 512 * (r.card : ℝ) by positivity))
  have htotal := (hbase.trans hreplace).trans (mul_le_mul_of_nonneg_right hcoeff hE)
  have habsR := mul_le_mul_of_nonneg_left habsorb (Nat.cast_nonneg r.card : (0 : ℝ) ≤ _)
  apply (le_div_iff₀ (sq_pos_of_pos hV)).mpr
  nlinarith

end LocalLargeValues

#print axioms LocalLargeValues.count_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``LocalLargeValues.count_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "LOCAL LARGE VALUES PASSED"
