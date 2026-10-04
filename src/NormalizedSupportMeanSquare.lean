import NormalizedMeanSquare
import PolynomialLogEnvelope

/-!
Continuous mean square for an arbitrary finite positive support with
separate lower and upper endpoints. The eventual envelope is uniform
over supports, coefficients, interval locations and vertical lines.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace NormalizedSupportMeanSquare
open Erdos374.HarmanGram152 Erdos374.HarmanAnalytic151MeanSquare

theorem bound (s : Finset ℕ) (coeff : ℕ → ℂ) (N B : ℕ)
    (a T E σ : ℝ) (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hs : ∀ n ∈ s, N ≤ n ∧ n ≤ B)
    (hT : 0 ≤ T) (hσ : 1 ≤ σ)
    (henergy : (∑ n ∈ s, ‖coeff n‖ ^ 2) ≤ E) :
    (∫ t in Icc a (a + T), ‖verticalDirichlet152 s coeff σ t‖ ^ 2) ≤
      (T + 4 * B * (1 + Real.log B)) * E / (N : ℝ) ^ 2 := by
  have hs0 : ∀ n ∈ s, 0 < n := by
    intro n hn
    have hh := (hs n hn).1
    omega
  let weighted : ℕ → ℂ := fun n => conj (normalizedCoefficients152 coeff σ n)
  have he : (∑ n ∈ s, ‖weighted n‖ ^ 2) ≤ E / (N : ℝ) ^ 2 := by
    dsimp [weighted]
    simp only [RCLike.norm_conj]
    exact (normalized_coefficients_energy152 s coeff N hN σ hσ
      (fun n hn => (hs n hn).1)).trans
        (div_le_div_of_nonneg_right henergy (sq_nonneg _))
  have hlog : 0 ≤ Real.log (B : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hB)
  have hm := dirichlet_mean_square_le151 s weighted B
    (fun n hn => ⟨by have hh := (hs n hn).1; omega, (hs n hn).2⟩) a (a + T)
  simp only [add_sub_cancel_left] at hm
  have hcoef : 0 ≤ T + 4 * (B : ℝ) * (1 + Real.log B) := by positivity
  have hbound := hm.trans (mul_le_mul_of_nonneg_left he hcoef)
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show a ≤ a + T by linarith)]
  simp_rw [verticalDirichlet_norm152 _ _ _ _ hs0]
  convert hbound using 1
  ring

/-- The algebraic envelope keeps the lower and upper lengths independent. -/
theorem length_energy_envelope (X N B T ε : ℝ)
    (hX : 1 ≤ X) (hε : 0 ≤ ε) (hN : 0 < N) (hB : 1 ≤ B)
    (hNscale : X ^ (1 - ε) ≤ N) (hBscale : B ≤ X ^ (1 + ε))
    (_hT : 0 ≤ T) (hTX : T ≤ X)
    (hlog : (5 + 4 * ε) * (1 + Real.log X) ≤ X ^ (3 * ε)) :
    (T + 4 * B * (1 + Real.log B)) * X ^ ε / N ≤ X ^ (6 * ε) := by
  have hXp : 0 < X := by linarith
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hlogBX : Real.log B ≤ (1 + ε) * Real.log X := by
    have hh := Real.log_le_log (by linarith : 0 < B) hBscale
    rwa [Real.log_rpow hXp] at hh
  have hXpower : X ≤ X ^ (1 + ε) := by
    calc
      X = X ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have hlength : T + 4 * B * (1 + Real.log B) ≤
      ((5 + 4 * ε) * (1 + Real.log X)) * X ^ (1 + ε) := by
    calc
      _ ≤ X ^ (1 + ε) + 4 * X ^ (1 + ε) *
          (1 + (1 + ε) * Real.log X) := by
        gcongr
        exact hTX.trans hXpower
      _ = (5 + 4 * (1 + ε) * Real.log X) * X ^ (1 + ε) := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith
  have hnormalized : X ^ ε / N ≤ X ^ (-1 + 2 * ε) := by
    calc
      X ^ ε / N ≤ X ^ ε / X ^ (1 - ε) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hNscale
      _ = X ^ (-1 + 2 * ε) := by
        rw [← Real.rpow_sub hXp]
        congr 1
        ring
  calc
    _ = (T + 4 * B * (1 + Real.log B)) * (X ^ ε / N) := by ring
    _ ≤ (((5 + 4 * ε) * (1 + Real.log X)) * X ^ (1 + ε)) *
        X ^ (-1 + 2 * ε) :=
      mul_le_mul hlength hnormalized (by positivity) (by positivity)
    _ = ((5 + 4 * ε) * (1 + Real.log X)) * X ^ (3 * ε) := by
      rw [mul_assoc, ← Real.rpow_add hXp]
      congr 2
      ring
    _ ≤ X ^ (3 * ε) * X ^ (3 * ε) :=
      mul_le_mul_of_nonneg_right hlog (by positivity)
    _ = X ^ (6 * ε) := by
      rw [← Real.rpow_add hXp]
      congr 1
      ring

theorem eventual_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      ∀ (s : Finset ℕ) (coeff : ℕ → ℂ) (N B : ℕ) (a T σ : ℝ),
        1 ≤ N → 1 ≤ B →
        (∀ n ∈ s, N ≤ n ∧ n ≤ B) →
        X ^ (1 - ε) ≤ (N : ℝ) → (B : ℝ) ≤ X ^ (1 + ε) →
        0 ≤ T → T ≤ X → 1 ≤ σ →
        (∑ n ∈ s, ‖coeff n‖ ^ 2) ≤ X ^ ε * N →
        (∫ t in Icc a (a + T), ‖verticalDirichlet152 s coeff σ t‖ ^ 2) ≤
          X ^ (6 * ε) := by
  filter_upwards [PolynomialLogEnvelope.eventually_bound (5 + 4 * ε) 1
    (3 * ε) (by linarith) (by linarith)] with X hh
  refine ⟨hh.1, ?_⟩
  intro s coeff N B a T σ hN hB hs hNscale hBscale hT hTX hσ henergy
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  apply (bound s coeff N B a T (X ^ ε * N) σ hN hB hs hT hσ henergy).trans
  calc
    _ = (T + 4 * (B : ℝ) * (1 + Real.log B)) * X ^ ε / N := by
      field_simp
    _ ≤ _ := length_energy_envelope X N B T ε hh.1 hε.le hNp
      (by exact_mod_cast hB) hNscale hBscale hT hTX (by simpa using hh.2)

end NormalizedSupportMeanSquare

#print axioms NormalizedSupportMeanSquare.bound
#print axioms NormalizedSupportMeanSquare.eventual_bound
run_cmd do
  for target in [``NormalizedSupportMeanSquare.bound,
      ``NormalizedSupportMeanSquare.length_energy_envelope,
      ``NormalizedSupportMeanSquare.eventual_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "NORMALIZED SUPPORT MEAN SQUARE PASSED"
