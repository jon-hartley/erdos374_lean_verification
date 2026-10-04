import NormalizedDyadicCap
import SmoothedDirichletKernel

/-!
Absolute coefficient mass on a strict dyadic interval, derived from
coefficient energy. The strict lower endpoint gives at most M terms.
This follows the counting and normalization of NormalizedDyadicCap.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace DyadicCoefficientEnergyMass
open SmoothedDirichletKernel

theorem sq_bound (s : Finset ℕ) (M : ℕ) (coeff : ℕ → ℂ) (σ A : ℝ)
    (hM : 1 ≤ M) (hσ : 1 ≤ σ) (_hA : 0 ≤ A)
    (hs : ∀ n ∈ s, M < n ∧ n ≤ 2 * M)
    (henergy : (∑ n ∈ s, ‖coeff n‖ ^ 2) ≤ A * M) :
    (coefficientMass s coeff σ) ^ 2 ≤ A := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hmass : coefficientMass s coeff σ ≤ (∑ n ∈ s, ‖coeff n‖) / M := by
    unfold coefficientMass
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro n hn
    have hMn : (M : ℝ) ≤ n := by exact_mod_cast (hs n hn).1.le
    have hp : (n : ℝ) ^ (-σ) ≤ (M : ℝ)⁻¹ := by
      calc
        _ ≤ (M : ℝ) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos hMp hMn (by linarith)
        _ ≤ (M : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hMone (by linarith)
        _ = _ := Real.rpow_neg_one _
    simpa only [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hp (norm_nonneg (coeff n))
  have hsum : (∑ n ∈ s, ‖coeff n‖) ^ 2 ≤ A * (M : ℝ) ^ 2 := by
    calc
      _ ≤ (s.card : ℝ) * ∑ n ∈ s, ‖coeff n‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
      _ ≤ (M : ℝ) * (A * M) :=
        mul_le_mul (NormalizedDyadicCap.card_bound s M hs) henergy
          (by positivity) hMp.le
      _ = _ := by ring
  calc
    _ ≤ ((∑ n ∈ s, ‖coeff n‖) / M) ^ 2 :=
      pow_le_pow_left₀ (mass_nonnegative s coeff σ) hmass 2
    _ = (∑ n ∈ s, ‖coeff n‖) ^ 2 / (M : ℝ) ^ 2 := div_pow _ _ _
    _ ≤ (A * (M : ℝ) ^ 2) / (M : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hsum (sq_nonneg _)
    _ = A := by field_simp

theorem rpow_bound (s : Finset ℕ) (M : ℕ) (coeff : ℕ → ℂ) (σ X β : ℝ)
    (hM : 1 ≤ M) (hσ : 1 ≤ σ) (hX : 0 < X)
    (hs : ∀ n ∈ s, M < n ∧ n ≤ 2 * M)
    (henergy : (∑ n ∈ s, ‖coeff n‖ ^ 2) ≤ X ^ β * M) :
    coefficientMass s coeff σ ≤ X ^ (β / 2) := by
  apply (sq_le_sq₀ (mass_nonnegative s coeff σ) (by positivity)).mp
  have hp : (X ^ (β / 2)) ^ 2 = X ^ β := by
    rw [← Real.rpow_mul_natCast hX.le]
    congr 1
    ring
  rw [hp]
  exact sq_bound s M coeff σ (X ^ β) hM hσ (by positivity) hs henergy

end DyadicCoefficientEnergyMass

#print axioms DyadicCoefficientEnergyMass.rpow_bound
run_cmd do
  for target in [``DyadicCoefficientEnergyMass.sq_bound,
      ``DyadicCoefficientEnergyMass.rpow_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "DYADIC COEFFICIENT ENERGY MASS PASSED"
