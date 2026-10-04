import FourfoldDivisorCoverage
import HarmanDivisorContour
import PolynomialLogEnvelope

/-!
Sharp signed counts for the entire fourfold divisor support have the
same finite-height contour approximation, with explicit common endpoints.
The second theorem expresses this error relative to a short-window scale.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter MeasureTheory Set

namespace FourfoldDivisorApproximation
open MellinCofactorCoverage HarmanDivisorContour

theorem eventually_bound : ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
    ∀ (A x δ : ℝ) (s : Finset ℕ) (weight : ℕ → ℝ),
      1 ≤ A → A ≤ X →
      (∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A) →
      (∀ d ∈ s, |weight d| ≤ X ^ (1 / 1600 : ℝ)) →
      x ∈ Icc X (2 * X) → δ ∈ Icc 0 (1 / 2) →
      ‖error s weight (lowerCutoff X A) (upperCutoff X A)
        (X ^ (-19 / 20 : ℝ)) (-X) X (1 + 1 / Real.log X) δ x‖ ≤
          4 * X ^ (2 / 25 : ℝ) := by
  filter_upwards [HarmanDivisorContour.eventual_approximation,
    eventually_ge_atTop (36 : ℝ)] with X hp hX
  refine ⟨hp.1, ?_⟩
  intro A x δ s weight hA hAX hs hw hx hδ
  have hXp : 0 < X := by linarith
  have hAp : 0 < A := by linarith
  have hD : 1 ≤ FourfoldDivisorCoverage.divisorCutoff A := by
    apply (Nat.le_floor_iff (by positivity : 0 ≤ 4 * A)).mpr
    norm_num
    linarith
  have hhi : 1 ≤ upperCutoff X A := by
    have hh : 0 < upperCutoff X A := Nat.ceil_pos.mpr (by positivity)
    omega
  have hbudget := FourfoldDivisorCoverage.product_budget X A hXp.le hAp hAX
  exact hp.2 s weight (FourfoldDivisorCoverage.divisorCutoff A)
    (lowerCutoff X A) (upperCutoff X A) x δ hD hhi
    (hbudget.trans (by nlinarith))
    (fun d hd => FourfoldDivisorCoverage.divisor_bounds A d hAp (hs d hd))
    hw hx hδ
    (fun d hd => (FourfoldDivisorCoverage.floor_coverage X A x δ d hXp hAp
      (hs d hd) hx hδ).1)
    (fun d hd => (FourfoldDivisorCoverage.floor_coverage X A x δ d hXp hAp
      (hs d hd) hx hδ).2)

theorem eventually_relative (θ : ℝ) (hθ : 2 / 25 < θ) :
    ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
      ∀ (A x δ Y : ℝ) (s : Finset ℕ) (weight : ℕ → ℝ),
        1 ≤ A → A ≤ X →
        (∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A) →
        (∀ d ∈ s, |weight d| ≤ X ^ (1 / 1600 : ℝ)) →
        x ∈ Icc X (2 * X) → δ ∈ Icc 0 (1 / 2) → X ^ θ ≤ Y →
        ‖error s weight (lowerCutoff X A) (upperCutoff X A)
          (X ^ (-19 / 20 : ℝ)) (-X) X (1 + 1 / Real.log X) δ x‖ ≤
            Y * X ^ (-((θ - 2 / 25) / 2)) := by
  filter_upwards [eventually_bound, PolynomialLogEnvelope.eventually_constant_bound
    4 ((θ - 2 / 25) / 2) (by norm_num) (by linarith)] with X hp hc
  refine ⟨hp.1, ?_⟩
  intro A x δ Y s weight hA hAX hs hw hx hδ hY
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hp.1
  apply (hp.2 A x δ s weight hA hAX hs hw hx hδ).trans
  calc
    _ ≤ X ^ ((θ - 2 / 25) / 2) * X ^ (2 / 25 : ℝ) :=
      mul_le_mul_of_nonneg_right hc.2 (by positivity)
    _ = X ^ θ * X ^ (-((θ - 2 / 25) / 2)) := by
      rw [← Real.rpow_add hXp, ← Real.rpow_add hXp]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hY (by positivity)

end FourfoldDivisorApproximation

#print axioms FourfoldDivisorApproximation.eventually_relative
run_cmd do
  for target in [``FourfoldDivisorApproximation.eventually_bound,
      ``FourfoldDivisorApproximation.eventually_relative] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "FOURFOLD DIVISOR APPROXIMATION PASSED"
