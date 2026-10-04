import ProductExpressionEnvelope
import NormalizedDyadicCap

/-!
Uniform small growth of real moments of the actual full mixed product.
Both coefficient families may have a quantified small energy loss. The
moment order may vary between two and three after the ambient cutoff is
chosen. The displayed length condition remains necessary input.
-/

set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace NormalizedProductGrowth
open Erdos374.HarmanGram152 ProductMomentExpression

theorem eventually_bound (γ : ℝ) (hγ : 0 < γ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      ∀ (K M : ℕ) (s r : Finset ℕ) (left right : ℕ → ℂ)
        (a T σ p : ℝ),
        1 ≤ K → 1 ≤ M → (K : ℝ) ≤ X → (M : ℝ) ≤ X →
        1 ≤ T → T ≤ X → 1 ≤ σ → 2 ≤ p → p ≤ 3 →
        T ^ (4 : ℕ) ≤ (K * M : ℕ) ^ (p + 2) →
        (∀ n ∈ s, K < n ∧ n ≤ 2 * K) →
        (∀ n ∈ r, M < n ∧ n ≤ 2 * M) →
        (∑ n ∈ s, ‖left n‖ ^ 2) ≤ X ^ ε * K →
        (∑ n ∈ r, ‖right n‖ ^ 2) ≤ X ^ ε * M →
        (∫ t in Icc a (a + T),
          ‖verticalDirichlet152 s left σ t *
            verticalDirichlet152 r right σ t‖ ^ p) ≤ X ^ γ := by
  let δ := γ / 4
  let ε := δ / 100
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hmargin : 3 * (2 * ε + (ε + ε)) < δ := by dsimp [ε]; linarith
  obtain ⟨D, hD, C, hC, hmoment⟩ := ProductMomentExpression.integral_bound ε hε
  refine ⟨ε, hε, ?_⟩
  filter_upwards [ProductExpressionEnvelope.eventually_growth_bound D C ε (ε + ε) ε δ
    hD hC hε.le (by positivity) hε.le hδ hmargin,
    PolynomialLogEnvelope.eventually_constant_bound 26 δ (by norm_num) hδ]
    with X he hc
  refine ⟨he.1, ?_⟩
  intro K M s r left right a T σ p hK hM hKX hMX hT hTX hσ hp hp3
    hlength hs hr heK heM
  have hXp : 0 < X := by linarith [he.1]
  have hTp : 0 < T := by linarith
  have hQ : 1 ≤ K * M := by nlinarith
  have hQX : (K * M : ℕ) ≤ X ^ 2 := by
    have hh := mul_le_mul hKX hMX (Nat.cast_nonneg M) hXp.le
    simpa only [Nat.cast_mul, pow_two] using hh
  have hcap : ∀ t ∈ Icc a (a + T),
      ‖verticalDirichlet152 s left σ t * verticalDirichlet152 r right σ t‖ ≤
        X ^ ε := by
    intro t _
    rw [norm_mul]
    calc
      _ ≤ X ^ (ε / 2) * X ^ (ε / 2) :=
        mul_le_mul
          (NormalizedDyadicCap.norm_le_rpow s K left σ t X ε hK hσ hXp hs heK)
          (NormalizedDyadicCap.norm_le_rpow r M right σ t X ε hM hσ hXp hr heM)
          (norm_nonneg _) (by positivity)
      _ = _ := by rw [← Real.rpow_add hXp]; congr 1; ring
  have hpower : (X ^ ε) ^ (p - 2) ≤ X ^ δ := by
    rw [← Real.rpow_mul hXp.le]
    apply Real.rpow_le_rpow_of_exponent_le he.1
    have hh := mul_le_mul_of_nonneg_left (show p - 2 ≤ 1 by linarith) hε.le
    dsimp [ε] at *
    linarith
  have hh := hmoment K M s r left right a T ε ε X σ (X ^ ε) p (X ^ δ)
    hK hM hTp hXp hσ (by positivity) hp (by linarith) (by positivity)
    hs hr heK heM hcap hpower
  calc
    _ ≤ upperBound D C (K * M) T ε (ε + ε) X (X ^ ε) p (X ^ δ) := hh
    _ ≤ 26 * X ^ (3 * δ) :=
      he.2 (K * M) T (X ^ ε) p hQ hQX hT hTX hp hp3 hlength le_rfl
    _ ≤ X ^ δ * X ^ (3 * δ) := mul_le_mul_of_nonneg_right hc.2 (by positivity)
    _ = X ^ γ := by
      rw [← Real.rpow_add hXp]
      congr 1
      dsimp [δ]
      ring

end NormalizedProductGrowth

#print axioms NormalizedProductGrowth.eventually_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``NormalizedProductGrowth.eventually_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "NORMALIZED PRODUCT GROWTH PASSED"
