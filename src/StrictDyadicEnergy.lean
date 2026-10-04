import NormalizedDyadicCap

/-! Real coefficient energy on a strict dyadic support. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace StrictDyadicEnergy

theorem bounded_real_energy (M : ℕ) (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ n ∈ s, M < n ∧ n ≤ 2 * M)
    (ha : ∀ n ∈ s, |a n| ≤ 1) :
    (∑ n ∈ s, (a n) ^ 2) ≤ M := by
  calc
    _ ≤ ∑ _n ∈ s, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hh := pow_le_pow_left₀ (abs_nonneg (a n)) (ha n hn) 2
      simpa only [sq_abs, one_pow] using hh
    _ = (s.card : ℝ) := by simp
    _ ≤ M := NormalizedDyadicCap.card_bound s M hs

end StrictDyadicEnergy

#print axioms StrictDyadicEnergy.bounded_real_energy
run_cmd do
  let axioms ← Lean.collectAxioms ``StrictDyadicEnergy.bounded_real_energy
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice ||
        ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "STRICT DYADIC ENERGY PASSED"
