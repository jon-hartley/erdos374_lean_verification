import DirichletCoefficientMass

/-!
Coefficient energy and absolute mass for coefficients of norm at most
one on any subset of [N,2N]. The extra endpoint costs a factor two.
This includes prime and sifted indicator coefficients on that support.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace BoundedDyadicCoefficients
open SmoothedDirichletKernel

theorem card_bound (s : Finset ℕ) (N : ℕ) (hN : 1 ≤ N)
    (hs : ∀ n ∈ s, N ≤ n ∧ n ≤ 2 * N) : (s.card : ℝ) ≤ 2 * N := by
  have hsub : s ⊆ Finset.Icc N (2 * N) := by
    intro n hn
    exact Finset.mem_Icc.mpr (hs n hn)
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hc
  have hh : s.card ≤ 2 * N := by omega
  exact_mod_cast hh

theorem energy_bound (s : Finset ℕ) (N : ℕ) (a : ℕ → ℂ) (hN : 1 ≤ N)
    (hs : ∀ n ∈ s, N ≤ n ∧ n ≤ 2 * N)
    (ha : ∀ n ∈ s, ‖a n‖ ≤ 1) :
    (∑ n ∈ s, ‖a n‖ ^ 2) ≤ 2 * N := by
  calc
    _ ≤ ∑ n ∈ s, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (ha n hn) 2
    _ = (s.card : ℝ) := by simp
    _ ≤ _ := card_bound s N hN hs

theorem mass_bound (s : Finset ℕ) (N : ℕ) (a : ℕ → ℂ) (σ : ℝ)
    (hN : 1 ≤ N) (hs : ∀ n ∈ s, N ≤ n ∧ n ≤ 2 * N)
    (ha : ∀ n ∈ s, ‖a n‖ ≤ 1) (hσ : 1 ≤ σ) :
    coefficientMass s a σ ≤ 2 := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  calc
    _ ≤ ∑ n ∈ s, (N : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hNn : (N : ℝ) ≤ n := by exact_mod_cast (hs n hn).1
      have hnp : (0 : ℝ) < n := hNp.trans_le hNn
      calc
        _ ≤ (n : ℝ) ^ (-σ) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right (ha n hn)
            (Real.rpow_nonneg hnp.le (-σ))
        _ ≤ (N : ℝ) ^ (-σ) := Real.rpow_le_rpow_of_nonpos hNp hNn (by linarith)
        _ ≤ (N : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
        _ = _ := Real.rpow_neg_one _
    _ = (s.card : ℝ) * (N : ℝ)⁻¹ := by simp
    _ ≤ (2 * N) * (N : ℝ)⁻¹ := mul_le_mul_of_nonneg_right (card_bound s N hN hs) (by positivity)
    _ = 2 := by field_simp

end BoundedDyadicCoefficients

#print axioms BoundedDyadicCoefficients.mass_bound
run_cmd do
  for target in [``BoundedDyadicCoefficients.energy_bound,
      ``BoundedDyadicCoefficients.mass_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "BOUNDED DYADIC COEFFICIENTS PASSED"
