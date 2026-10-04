import FiniteCountApproximation
import SmoothedRapidKernel

/-!
Finite sharp-count approximation using any fixed smoothing derivative
order. Both the boundary allowance and the improved truncation error
remain explicit, with the order chosen before the scale.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RapidSmoothedPerron
open SmoothedCountBoundary SmoothedDirichletKernel

theorem approximation (k : ℕ) (Ψ : ℝ → ℝ) (hdiff : ContDiff ℝ ∞ Ψ)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hnonneg : ∀ x > 0, 0 ≤ Ψ x) (hmass : ∫ x in Ioi 0, Ψ x / x = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset ℕ) (weight : ℕ → ℝ) (ε X σ T W : ℝ),
      0 < X → (∀ n ∈ s, 0 < n) → 1 < σ → σ ≤ 2 → ε ∈ Ioo 0 1 → 0 < T → 0 ≤ W →
      (∀ n ∈ s, 0 ≤ weight n ∧ weight n ≤ W) →
      ‖(sharp s weight X : ℂ) - ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t in Icc (-T) T, integrand s (fun n => (weight n : ℂ)) Ψ ε X σ t‖ ≤
          W * (4 * Real.log 2 * ε * X + 1) +
          (1 / (2 * Real.pi)) *
            (2 * coefficientMass s (fun n => (weight n : ℂ)) σ * C * X ^ σ /
              (((k + 1 : ℕ) : ℝ) * (ε * T) ^ (k + 1))) := by
  obtain ⟨C, hC, htail⟩ := SmoothedRapidKernel.truncation_bound k Ψ hdiff hsupport hnonneg hmass
  refine ⟨C, hC, ?_⟩
  intro s weight ε X σ T W hX hs hσ hσtwo hε hT hW hweight
  exact FiniteCountApproximation.of_tail Ψ (hdiff.of_le (by simp)) hsupport hnonneg hmass
    s weight ε X σ T W _ hX hs hσ hσtwo hε hW hweight
    (htail s (fun n => (weight n : ℂ)) ε X σ T hX hs hσ hσtwo hε hT)

end RapidSmoothedPerron

#print axioms RapidSmoothedPerron.approximation
run_cmd do
  let axioms ← Lean.collectAxioms ``RapidSmoothedPerron.approximation
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "RAPID SMOOTHED PERRON PASSED"
