import SmoothedDirichletKernel
import BoundaryMassBound

/-!
Shared counting-approximation step. An absolute truncation error R is
combined with the proved smoothing boundary error and Mellin inversion.
Specific tail estimates are supplied by the calling theorems.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace FiniteCountApproximation
open SmoothedCountBoundary SmoothedDirichletKernel

theorem of_tail (Ψ : ℝ → ℝ) (hdiff : ContDiff ℝ 1 Ψ)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hnonneg : ∀ x > 0, 0 ≤ Ψ x) (hmass : ∫ x in Ioi 0, Ψ x / x = 1)
    (s : Finset ℕ) (weight : ℕ → ℝ) (ε X σ T W R : ℝ)
    (hX : 0 < X) (hs : ∀ n ∈ s, 0 < n) (hσ : 1 < σ) (hσtwo : σ ≤ 2)
    (hε : ε ∈ Ioo 0 1) (hW : 0 ≤ W)
    (hweight : ∀ n ∈ s, 0 ≤ weight n ∧ weight n ≤ W)
    (htail : ‖(∫ t : ℝ, integrand s (fun n => (weight n : ℂ)) Ψ ε X σ t) -
      ∫ t in Icc (-T) T, integrand s (fun n => (weight n : ℂ)) Ψ ε X σ t‖ ≤ R) :
    ‖(sharp s weight X : ℂ) - ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t in Icc (-T) T, integrand s (fun n => (weight n : ℂ)) Ψ ε X σ t‖ ≤
        W * (4 * Real.log 2 * ε * X + 1) + (1 / (2 * Real.pi)) * R := by
  let coeff := fun n => (weight n : ℂ)
  let c : ℝ := 1 / (2 * Real.pi)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hinv := FiniteMellinInversion.smooth_finite_sum s coeff Ψ X σ ε hX hs
    hσ hσtwo hε hdiff hnonneg hsupport hmass
  have hidentity : (smooth s weight Ψ ε X : ℂ) =
      (c : ℂ) * ∫ t : ℝ, integrand s coeff Ψ ε X σ t := by
    simpa only [smooth, Complex.ofReal_sum, Complex.ofReal_mul, integrand, coeff, c] using hinv
  have hboundary : ‖(sharp s weight X : ℂ) - (smooth s weight Ψ ε X : ℂ)‖ ≤
      W * (4 * Real.log 2 * ε * X + 1) := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    exact (error_bound s weight Ψ ε X hX hε hs (fun n hn => (hweight n hn).1)
      hnonneg hsupport hmass).trans
      (BoundaryMassBound.boundary_bound s weight ε X W hX hε.1.le hW
        (fun n hn => (hweight n hn).2))
  have hfrequency : ‖(smooth s weight Ψ ε X : ℂ) -
      (c : ℂ) * ∫ t in Icc (-T) T, integrand s coeff Ψ ε X σ t‖ ≤
      c * (R) := by
    rw [hidentity, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left htail hc
  calc
    _ = ‖((sharp s weight X : ℂ) - (smooth s weight Ψ ε X : ℂ)) +
        ((smooth s weight Ψ ε X : ℂ) -
          (c : ℂ) * ∫ t in Icc (-T) T, integrand s coeff Ψ ε X σ t)‖ := by
      congr 1
      dsimp [c, coeff]
      ring
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add hboundary hfrequency)

end FiniteCountApproximation

#print axioms FiniteCountApproximation.of_tail
run_cmd do
  let axioms ← Lean.collectAxioms ``FiniteCountApproximation.of_tail
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "FINITE COUNT APPROXIMATION PASSED"
