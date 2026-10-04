import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-! Explicit logarithmic bounds for the real reciprocal sum used in the
finite near-integer layer argument. The empty sum is handled explicitly. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace Item1HarmonicBound

/-- The real range sum is the cast of Mathlib's rational harmonic number. -/
theorem sum_range_reciprocal_eq_harmonic (N : ℕ) :
    (∑ k ∈ Finset.range N, 1/((k:ℝ)+1)) = (harmonic N:ℝ) := by
  simp [harmonic, one_div]

/-- The zero-length reciprocal sum is zero. -/
theorem sum_range_reciprocal_zero :
    (∑ k ∈ Finset.range 0, 1/((k:ℝ)+1)) = 0 := by simp

theorem sum_range_reciprocal_nonneg (N : ℕ) :
    0 ≤ ∑ k ∈ Finset.range N, 1/((k:ℝ)+1) := by
  exact Finset.sum_nonneg (fun k _ => by positivity)

/-- The usual bound with a positive natural length. -/
theorem sum_range_reciprocal_le_log (N : ℕ) (_hN : 1 ≤ N) :
    (∑ k ∈ Finset.range N, 1/((k:ℝ)+1)) ≤ 1+Real.log (N:ℝ) := by
  rw [sum_range_reciprocal_eq_harmonic]
  exact harmonic_le_one_add_log N

/-- A uniform version whose logarithm always has an argument at least one. -/
theorem sum_range_reciprocal_le_log_max (N : ℕ) :
    (∑ k ∈ Finset.range N, 1/((k:ℝ)+1)) ≤ 1+Real.log (max 1 (N:ℝ)) := by
  by_cases hN : 1 ≤ N
  · have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
    rw [max_eq_right hN']
    exact sum_range_reciprocal_le_log N hN
  · have hzero : N = 0 := by omega
    simp [hzero]

/-- The convenient all-length estimate with log(N+1). -/
theorem sum_range_reciprocal_le_log_succ (N : ℕ) :
    (∑ k ∈ Finset.range N, 1/((k:ℝ)+1)) ≤ 1+Real.log ((N:ℝ)+1) := by
  apply (sum_range_reciprocal_le_log_max N).trans
  apply add_le_add le_rfl
  apply Real.log_le_log
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    exact max_le (by linarith) (by linarith)

end Item1HarmonicBound

run_cmd do
  for target in [``Item1HarmonicBound.sum_range_reciprocal_eq_harmonic,
      ``Item1HarmonicBound.sum_range_reciprocal_zero,
      ``Item1HarmonicBound.sum_range_reciprocal_nonneg,
      ``Item1HarmonicBound.sum_range_reciprocal_le_log,
      ``Item1HarmonicBound.sum_range_reciprocal_le_log_max,
      ``Item1HarmonicBound.sum_range_reciprocal_le_log_succ] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "HARMONIC BOUND: 6 standard-axiom theorem guards passed."
