import NormalizedMeanSquare

/-!
Uniform norm bounds from coefficient energy on a strict dyadic interval.
The support has at most M terms and normalization reduces its energy by
M squared. Finite Cauchy-Schwarz then gives the bound without any
individual coefficient bound.

The normalization follows NormalizedMeanSquare; the support count follows
BoundedDyadicCoefficients, with the strict lower endpoint retained.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace NormalizedDyadicCap
open Erdos374.HarmanGram152 Erdos374.HarmanAnalytic151MeanSquare

theorem card_bound (s : Finset ℕ) (M : ℕ)
    (hs : ∀ n ∈ s, M < n ∧ n ≤ 2 * M) : (s.card : ℝ) ≤ M := by
  have hsub : s ⊆ Finset.Ioc M (2 * M) := by
    intro n hn
    exact Finset.mem_Ioc.mpr (hs n hn)
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Ioc] at hc
  have hh : s.card ≤ M := by omega
  exact_mod_cast hh

theorem norm_sq_le_energy (s : Finset ℕ) (M : ℕ) (coeff : ℕ → ℂ)
    (σ t A : ℝ) (hM : 1 ≤ M) (hσ : 1 ≤ σ) (hA : 0 ≤ A)
    (hs : ∀ n ∈ s, M < n ∧ n ≤ 2 * M)
    (henergy : (∑ n ∈ s, ‖coeff n‖ ^ 2) ≤ A * M) :
    ‖verticalDirichlet152 s coeff σ t‖ ^ 2 ≤ A := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hs0 : ∀ n ∈ s, 0 < n := by
    intro n hn
    have hh := (hs n hn).1
    omega
  have he : (∑ n ∈ s, ‖normalizedCoefficients152 coeff σ n‖ ^ 2) ≤
      A / M := by
    apply (normalized_coefficients_energy152 s coeff M hM σ hσ
      (fun n hn => (hs n hn).1.le)).trans
    calc
      _ ≤ (A * M) / (M : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right henergy (sq_nonneg _)
      _ = _ := by field_simp
  have hn := Erdos374.ExponentialSum151.norm_sum_sq_le_card_energy s
    (fun n => normalizedCoefficients152 coeff σ n *
      exponentialKernel151 (Real.log n) (-t))
  simp only [norm_mul, norm_kernel151, mul_one] at hn
  rw [verticalDirichlet_eq_exponential152 s coeff σ t hs0]
  unfold exponentialSum151
  calc
    _ ≤ (s.card : ℝ) *
        (∑ n ∈ s, ‖normalizedCoefficients152 coeff σ n‖ ^ 2) := hn
    _ ≤ (s.card : ℝ) * (A / M) :=
      mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)
    _ ≤ (M : ℝ) * (A / M) :=
      mul_le_mul_of_nonneg_right (card_bound s M hs) (div_nonneg hA hMp.le)
    _ = A := by field_simp

theorem norm_le_rpow (s : Finset ℕ) (M : ℕ) (coeff : ℕ → ℂ)
    (σ t X β : ℝ) (hM : 1 ≤ M) (hσ : 1 ≤ σ) (hX : 0 < X)
    (hs : ∀ n ∈ s, M < n ∧ n ≤ 2 * M)
    (henergy : (∑ n ∈ s, ‖coeff n‖ ^ 2) ≤ X ^ β * M) :
    ‖verticalDirichlet152 s coeff σ t‖ ≤ X ^ (β / 2) := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.rpow_nonneg hX.le _)).mp
  have hpow : (X ^ (β / 2)) ^ 2 = X ^ β := by
    rw [← Real.rpow_mul_natCast hX.le]
    congr 1
    ring
  rw [hpow]
  exact norm_sq_le_energy s M coeff σ t (X ^ β) hM hσ
    (Real.rpow_nonneg hX.le _) hs henergy

end NormalizedDyadicCap

#print axioms NormalizedDyadicCap.norm_sq_le_energy
#print axioms NormalizedDyadicCap.norm_le_rpow
run_cmd do
  for target in [``NormalizedDyadicCap.card_bound,
      ``NormalizedDyadicCap.norm_sq_le_energy,
      ``NormalizedDyadicCap.norm_le_rpow] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "NORMALIZED DYADIC CAP PASSED"
