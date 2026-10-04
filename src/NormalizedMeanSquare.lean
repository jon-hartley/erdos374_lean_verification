import NormalizedLargeValues

/-!
Continuity and classical continuous mean square for actual vertical
Dirichlet polynomials. The n^(-sigma) coefficient normalization and
the source support endpoints are explicit.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace NormalizedMeanSquare
open Erdos374.HarmanGram152 Erdos374.HarmanAnalytic151MeanSquare

theorem continuous_vertical (s : Finset ℕ) (coeff : ℕ → ℂ) (σ : ℝ)
    (hs : ∀ n ∈ s, 0 < n) : Continuous (verticalDirichlet152 s coeff σ) := by
  have heq : verticalDirichlet152 s coeff σ =
      fun t => exponentialSum151 s (normalizedCoefficients152 coeff σ) (fun n => Real.log n) (-t) :=
    funext (fun t => verticalDirichlet_eq_exponential152 s coeff σ t hs)
  rw [heq]
  exact (continuous_sum151 s _ _).comp continuous_neg

theorem mean_square_bound (N lo hi : ℕ) (coeff : ℕ → ℂ)
    (a T A σ : ℝ) (hN : 1 ≤ N) (hlo : N ≤ lo) (hhi : hi ≤ 2 * N)
    (hT : 0 ≤ T) (hσ : 1 ≤ σ)
    (henergy : (∑ n ∈ Finset.Ioc lo hi, ‖coeff n‖ ^ 2) ≤ A * N) :
    (∫ t in Icc a (a + T), ‖verticalDirichlet152 (Finset.Ioc lo hi) coeff σ t‖ ^ 2) ≤
      A * (T / N + 8 * (1 + Real.log (2 * N))) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs : ∀ n ∈ Finset.Ioc lo hi, N ≤ n ∧ n ≤ 2 * N := by
    intro n hn
    have hh := Finset.mem_Ioc.mp hn
    omega
  have hs0 : ∀ n ∈ Finset.Ioc lo hi, 0 < n := by
    intro n hn
    have hh := (hs n hn).1
    omega
  let weighted : ℕ → ℂ := fun n => conj (normalizedCoefficients152 coeff σ n)
  have he : (∑ n ∈ Finset.Ioc lo hi, ‖weighted n‖ ^ 2) ≤ A / N := by
    dsimp [weighted]
    simp only [RCLike.norm_conj]
    apply (normalized_coefficients_energy152 (Finset.Ioc lo hi) coeff N hN σ hσ
      (fun n hn => (hs n hn).1)).trans
    calc
      _ ≤ (A * N) / (N : ℝ) ^ 2 := div_le_div_of_nonneg_right henergy (sq_nonneg _)
      _ = _ := by field_simp
  have hlog : 0 ≤ Real.log (2 * (N : ℝ)) := Real.log_nonneg (by
    have hh : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith)
  have hm := dirichlet_mean_square_le151 (Finset.Ioc lo hi) weighted (2 * N)
    (fun n hn => ⟨by have hh := (hs n hn).1; omega, (hs n hn).2⟩) a (a + T)
  simp only [add_sub_cancel_left, Nat.cast_mul, Nat.cast_ofNat] at hm
  have hcoef : 0 ≤ T + 4 * (2 * (N : ℝ)) * (1 + Real.log (2 * N)) := by positivity
  have hbound := hm.trans (mul_le_mul_of_nonneg_left he hcoef)
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show a ≤ a + T by linarith)]
  simp_rw [verticalDirichlet_norm152 _ _ _ _ hs0]
  convert hbound using 1
  field_simp
  ring

end NormalizedMeanSquare

#print axioms NormalizedMeanSquare.mean_square_bound
run_cmd do
  for target in [``NormalizedMeanSquare.continuous_vertical,
      ``NormalizedMeanSquare.mean_square_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "NORMALIZED MEAN SQUARE PASSED"
