import HuxleyLogLoss

/-!
Large values for the actual vertical Dirichlet polynomial at sigma>=1.
A bounds the average squared unnormalized coefficient size. The
normalization by n^sigma is proved using the seed's exact norm identity.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators ComplexConjugate

namespace NormalizedLargeValues
open Erdos374.HarmanGram152 Erdos374.HarmanAnalytic151MeanSquare

theorem count_bound (N lo hi : ℕ) (coeff : ℕ → ℂ)
    (r : Finset ℝ) (a T A V σ : ℝ)
    (hN : 1 ≤ N) (hlo : N ≤ lo) (hhi : hi ≤ 2 * N)
    (hT : 0 ≤ T) (hA : 0 < A) (hV : 0 < V) (hσ : 1 ≤ σ)
    (henergy : (∑ n ∈ Finset.Ioc lo hi, ‖coeff n‖ ^ 2) ≤ A * N)
    (hrange : ∀ t ∈ r, a ≤ t ∧ t ≤ a + T)
    (hsep : ∀ x ∈ r, ∀ y ∈ r, x ≠ y → 1 ≤ |x - y|)
    (hlarge : ∀ t ∈ r, V ≤ ‖verticalDirichlet152 (Finset.Ioc lo hi) coeff σ t‖) :
    (r.card : ℝ) ≤ 258 * (1 + Real.log (T + 1)) *
      (A / V ^ 2 + 1024 ^ 2 * T * A ^ 3 *
        (1 + Real.log ((N : ℝ) + 1)) / ((N : ℝ) ^ 2 * V ^ 6)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs : ∀ n ∈ Finset.Ioc lo hi, N ≤ n := by
    intro n hn
    have hh := (Finset.mem_Ioc.mp hn).1
    omega
  have hs0 : ∀ n ∈ Finset.Ioc lo hi, 0 < n := by
    intro n hn
    have hh := hs n hn
    omega
  let weighted : ℕ → ℂ := fun n => conj (normalizedCoefficients152 coeff σ n)
  have he : (∑ n ∈ Finset.Ioc lo hi, ‖weighted n‖ ^ 2) ≤ A / N := by
    dsimp [weighted]
    simp only [RCLike.norm_conj]
    apply (normalized_coefficients_energy152 (Finset.Ioc lo hi) coeff N hN σ hσ hs).trans
    calc
      _ ≤ (A * N) / (N : ℝ) ^ 2 := div_le_div_of_nonneg_right henergy (sq_nonneg _)
      _ = _ := by field_simp
  have hh := HuxleyLogLoss.count_bound N lo hi weighted r a T (A / N) V
    hN hlo hhi hT (div_pos hA hNp) hV he hrange hsep (by
      intro t ht
      simpa only [verticalDirichlet_norm152 _ _ _ _ hs0] using hlarge t ht)
  convert hh using 1
  field_simp

end NormalizedLargeValues

#print axioms NormalizedLargeValues.count_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``NormalizedLargeValues.count_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "NORMALIZED LARGE VALUES PASSED"
