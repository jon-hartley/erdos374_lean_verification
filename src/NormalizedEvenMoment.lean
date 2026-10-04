import DirichletEvenMoment

/-!
Every fixed even moment of an actual normalized Dirichlet polynomial
has the expected time/length term and an arbitrary positive power loss.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace NormalizedEvenMoment
open Erdos374.HarmanGram152 Erdos374.HarmanAnalytic151MeanSquare

theorem integral_bound (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (s : Finset ℕ) (N : ℕ) (coeff : ℕ → ℂ) (a T A σ : ℝ),
      1 ≤ N → 0 ≤ T → 1 ≤ σ →
      (∀ n ∈ s, N ≤ n ∧ n ≤ 2 * N) →
      (∑ n ∈ s, ‖coeff n‖ ^ 2) ≤ A * N →
      (∫ t in Icc a (a + T), ‖verticalDirichlet152 s coeff σ t‖ ^ (2 * k)) ≤
        D * (2 * (N : ℝ)) ^ ε * A ^ k *
          (T / (N : ℝ) ^ k + 4 * (2 : ℝ) ^ k * (1 + k * Real.log (2 * N))) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  obtain ⟨D, hD, hmoment⟩ := DirichletEvenMoment.integral_bound k hk
    (ε / k) (div_pos hε hkpos)
  refine ⟨D, hD, ?_⟩
  intro s N coeff a T A σ hN hT hσ hs henergy
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs0 : ∀ n ∈ s, 0 < n := by
    intro n hn
    have hh := (hs n hn).1
    omega
  let weighted : ℕ → ℂ := fun n => conj (normalizedCoefficients152 coeff σ n)
  have he : (∑ n ∈ s, ‖weighted n‖ ^ 2) ≤ A / N := by
    dsimp [weighted]
    simp only [RCLike.norm_conj]
    apply (normalized_coefficients_energy152 s coeff N hN σ hσ
      (fun n hn => (hs n hn).1)).trans
    calc
      _ ≤ (A * N) / (N : ℝ) ^ 2 := div_le_div_of_nonneg_right henergy (sq_nonneg _)
      _ = _ := by field_simp
  have hsum : 0 ≤ ∑ n ∈ s, ‖weighted n‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hlog : 0 ≤ Real.log (((2 * N) ^ k : ℕ) : ℝ) := Real.log_nonneg (by
    exact_mod_cast one_le_pow₀ (show 1 ≤ 2 * N by omega) (n := k))
  have hf : 0 ≤ D * (((2 * N) ^ k : ℕ) : ℝ) ^ (ε / k) *
      (T + 4 * ((2 * N) ^ k : ℕ) * (1 + Real.log ((2 * N) ^ k : ℕ))) := by positivity
  have hh := (hmoment s (2 * N) weighted a T (by omega) hT
    (fun n hn => ⟨hs0 n hn, (hs n hn).2⟩)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsum he k) hf)
  have hpower : ((((2 * N) ^ k : ℕ) : ℝ) ^ (ε / k)) = (2 * (N : ℝ)) ^ ε := by
    rw [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, ← Real.rpow_natCast_mul (by positivity)]
    congr 1
    field_simp
  rw [hpower] at hh
  simp_rw [verticalDirichlet_norm152 s coeff σ _ hs0]
  apply hh.trans_eq
  rw [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, Real.log_pow, div_pow, mul_pow]
  field_simp

end NormalizedEvenMoment

#print axioms NormalizedEvenMoment.integral_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``NormalizedEvenMoment.integral_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "NORMALIZED EVEN MOMENT PASSED"
