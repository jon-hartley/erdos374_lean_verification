import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! Finite power-mean and weighted Cauchy inequalities for complex sums.
All sums retain their original finite index sets, including the empty set.
These inequalities contain no analytic cancellation hypothesis. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators

namespace Item1FiniteMomentHolder

/-- The finite power-mean inequality applied to the norms of complex terms. -/
theorem sum_norm_pow_le {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (p : ℕ) (hp : 1 ≤ p) :
    (∑ i ∈ s, ‖z i‖) ^ p ≤
      (s.card : ℝ) ^ (p - 1) * (∑ i ∈ s, ‖z i‖ ^ p) := by
  have hp' : p - 1 + 1 = p := Nat.sub_add_cancel hp
  have hh := pow_sum_le_card_mul_sum_pow (s := s) (f := fun i => ‖z i‖)
    (fun i _ => norm_nonneg (z i)) (p - 1)
  simpa only [hp'] using hh

/-- Triangle inequality followed by the finite power-mean inequality. -/
theorem norm_sum_pow_le {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (p : ℕ) (hp : 1 ≤ p) :
    ‖∑ i ∈ s, z i‖ ^ p ≤
      (s.card : ℝ) ^ (p - 1) * (∑ i ∈ s, ‖z i‖ ^ p) := by
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s z) p).trans
    (sum_norm_pow_le s z p hp)

theorem sum_norm_even_pow_le {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (r : ℕ) (hr : 1 ≤ r) :
    (∑ i ∈ s, ‖z i‖) ^ (2 * r) ≤
      (s.card : ℝ) ^ (2 * r - 1) * (∑ i ∈ s, ‖z i‖ ^ (2 * r)) :=
  sum_norm_pow_le s z (2 * r) (by omega)

theorem norm_sum_even_pow_le {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (r : ℕ) (hr : 1 ≤ r) :
    ‖∑ i ∈ s, z i‖ ^ (2 * r) ≤
      (s.card : ℝ) ^ (2 * r - 1) * (∑ i ∈ s, ‖z i‖ ^ (2 * r)) :=
  norm_sum_pow_le s z (2 * r) (by omega)

/-- Weighted Cauchy-Schwarz for arbitrary complex weights and values. -/
theorem weighted_cauchy_complex {ι : Type*} (s : Finset ι)
    (w V : ι → ℂ) :
    ‖∑ i ∈ s, w i * V i‖ ^ 2 ≤
      (∑ i ∈ s, ‖w i‖ ^ 2) * (∑ i ∈ s, ‖V i‖ ^ 2) := by
  have hnorm : ‖∑ i ∈ s, w i * V i‖ ≤ ∑ i ∈ s, ‖w i‖ * ‖V i‖ := by
    simpa only [norm_mul] using norm_sum_le s (fun i => w i * V i)
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖w i‖) (fun i => ‖V i‖))

/-- Real weights need no nonnegativity hypothesis because their squares
appear in the bound. This includes finite multiplicities as a special case. -/
theorem weighted_cauchy_real {ι : Type*} (s : Finset ι)
    (n : ι → ℝ) (V : ι → ℂ) :
    ‖∑ i ∈ s, (n i : ℂ) * V i‖ ^ 2 ≤
      (∑ i ∈ s, n i ^ 2) * (∑ i ∈ s, ‖V i‖ ^ 2) := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using
    weighted_cauchy_complex s (fun i => (n i : ℂ)) V

end Item1FiniteMomentHolder

run_cmd do
  for target in [``Item1FiniteMomentHolder.sum_norm_pow_le,
      ``Item1FiniteMomentHolder.norm_sum_pow_le,
      ``Item1FiniteMomentHolder.sum_norm_even_pow_le,
      ``Item1FiniteMomentHolder.norm_sum_even_pow_le,
      ``Item1FiniteMomentHolder.weighted_cauchy_complex,
      ``Item1FiniteMomentHolder.weighted_cauchy_real] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "FINITE MOMENT HOLDER: 6 standard-axiom theorem guards passed."
