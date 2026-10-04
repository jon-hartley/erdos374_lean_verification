import DirichletProductCoefficients
import PolynomialLogEnvelope

/-!
Pointwise coefficient bounds for a full finite convolution. Every
representation is retained. A divisor bound absorbs its multiplicity
into an arbitrarily small fixed power of the ambient scale.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter
open scoped BigOperators

namespace ProductCoefficientCap
open DirichletProductCoefficients

theorem norm_bound (s r : Finset ℕ) (left right : ℕ → ℂ) (n : ℕ) (A B : ℝ)
    (hn : n ≠ 0) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hleft : ∀ d ∈ s, ‖left d‖ ≤ A) (hright : ∀ k ∈ r, ‖right k‖ ≤ B) :
    ‖coefficient s r left right n‖ ≤ (n.divisors.card : ℝ) ^ 2 * A * B := by
  let fiber := (s ×ˢ r).filter (fun pair => productIndex pair = n)
  have hcard : (fiber.card : ℝ) ≤ (n.divisors.card : ℝ) ^ 2 := by
    exact_mod_cast fiber_card_bound s r n hn
  calc
    _ ≤ ∑ pair ∈ fiber, ‖pairWeight left right pair‖ := norm_sum_le _ _
    _ ≤ ∑ _pair ∈ fiber, A * B := by
      apply Finset.sum_le_sum
      intro pair hp
      have hpair := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      dsimp [pairWeight]
      rw [norm_mul]
      exact mul_le_mul (hleft _ hpair.1) (hright _ hpair.2) (norm_nonneg _) hA
    _ = (fiber.card : ℝ) * (A * B) := by simp
    _ ≤ (n.divisors.card : ℝ) ^ 2 * (A * B) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg hA hB)
    _ = _ := by ring

theorem eventually_bound (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      ∀ (s r : Finset ℕ) (left right : ℕ → ℂ) (n : ℕ),
        0 < n → (n : ℝ) ≤ X ^ (2 : ℕ) →
        (∀ d ∈ s, ‖left d‖ ≤ X ^ (δ / 8)) →
        (∀ k ∈ r, ‖right k‖ ≤ X ^ (δ / 8)) →
        ‖coefficient s r left right n‖ ≤ X ^ δ := by
  obtain ⟨D, hD, hdiv⟩ := DirichletPowerEnergy.divisor_power_bound 2 (by omega)
    (δ / 8) (by positivity)
  filter_upwards [PolynomialLogEnvelope.eventually_constant_bound D (δ / 2)
    hD.le (by positivity)] with X hX
  refine ⟨hX.1, ?_⟩
  intro s r left right n hn hnX hl hr
  have hXp : 0 < X := by linarith [hX.1]
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hpower : (n : ℝ) ^ (δ / 8) ≤ X ^ (δ / 4) := by
    calc
      _ ≤ (X ^ (2 : ℕ)) ^ (δ / 8) := Real.rpow_le_rpow hnp.le hnX (by positivity)
      _ = _ := by rw [← Real.rpow_natCast_mul hXp.le]; congr 1; ring
  calc
    _ ≤ (n.divisors.card : ℝ) ^ 2 * X ^ (δ / 8) * X ^ (δ / 8) :=
      norm_bound s r left right n (X ^ (δ / 8)) (X ^ (δ / 8))
        (by omega) (by positivity) (by positivity) hl hr
    _ ≤ (D * (n : ℝ) ^ (δ / 8)) * X ^ (δ / 8) * X ^ (δ / 8) := by gcongr; exact hdiv n
    _ ≤ (X ^ (δ / 2) * X ^ (δ / 4)) * X ^ (δ / 8) * X ^ (δ / 8) := by gcongr; exact hX.2
    _ = X ^ δ := by
      rw [← Real.rpow_add hXp, ← Real.rpow_add hXp, ← Real.rpow_add hXp]
      congr 1
      ring

end ProductCoefficientCap

#print axioms ProductCoefficientCap.eventually_bound
run_cmd do
  for target in [``ProductCoefficientCap.norm_bound,
      ``ProductCoefficientCap.eventually_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "PRODUCT COEFFICIENT CAP PASSED"
