import FourfoldDivisorCoverage
import CofactorMainTermBudget
import SignedDivisorErrorDecomposition

/-!
The actual full continuous contour for divisors in (A,4A] equals the
smoothed reciprocal-mass main term used in the error decomposition.
This keeps the same cofactor endpoints as all frequency estimates.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace FourfoldCofactorMainTerm
open ContinuousCofactorMellin MellinSmoothingFunction MellinCofactorCoverage
open Erdos374.HarmanGram152 MellinWindowFactor

theorem contour_eq (X A x δ ε σ : ℝ) (s : Finset ℕ) (coeff : ℕ → ℂ)
    (hX : 0 < X) (hA : 0 < A)
    (hx : x ∈ Icc X (2 * X)) (hδ : δ ∈ Icc 0 (1 / 2))
    (hε : ε ∈ Ioo 0 (1 / 4)) (hσ : 1 < σ) (hσtwo : σ ≤ 2)
    (hlo : 1 ≤ lowerCutoff X A)
    (hs : ∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A) :
    CofactorMainTermBudget.coveredContour X A x δ ε σ s coeff =
      ((x * δ : ℝ) : ℂ) *
        mellin (fun y => (Smooth1 smoothing ε y : ℂ)) 1 *
          (∑ d ∈ s, coeff d / (d : ℂ)) := by
  have hxp : 0 < x := hX.trans_le hx.1
  have hleft : 0 < x - x * δ := by
    have hw := DyadicDivisorWindow.window_bounds X x δ hX hx hδ
    linarith [hw.1]
  have ha : (0 : ℝ) < lowerCutoff X A := by
    exact_mod_cast (show 0 < lowerCutoff X A by omega)
  have hab : (lowerCutoff X A : ℝ) ≤ upperCutoff X A := by
    exact_mod_cast (cutoff_strict X A hX hA).le
  have hεone : ε ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hε.1, hε.2]
  have hpos : ∀ d ∈ s, 0 < d := by
    intro d hd
    exact_mod_cast hA.trans (hs d hd).1
  have hm (d : ℕ) (hd : d ∈ s) :=
    FourfoldDivisorCoverage.transition_margins X A x δ ε d hX hA (hs d hd) hx hδ hε
  have hmain := finite_continuous_main_term s coeff smoothing ε x
    (x - x * δ) (lowerCutoff X A : ℝ) (upperCutoff X A : ℝ)
    hxp hleft ha hab hpos hεone differentiable nonnegative support mass_one
    (fun d hd => (hm d hd).1) (fun d hd => (hm d hd).2.1)
    (fun d hd => (hm d hd).2.2.1) (fun d hd => (hm d hd).2.2.2)
  rw [finite_short_window_integrand s coeff smoothing ε σ x (x - x * δ)
    (lowerCutoff X A : ℝ) (upperCutoff X A : ℝ) hxp hleft ha hab hpos
    hσ hσtwo hεone differentiable nonnegative support mass_one] at hmain
  simpa only [show x - (x - x * δ) = x * δ by ring,
    CofactorMainTermBudget.coveredContour] using hmain

theorem signed_contour_eq (X A x δ ε σ : ℝ) (s : Finset ℕ) (weight : ℕ → ℝ)
    (hX : 0 < X) (hA : 0 < A)
    (hx : x ∈ Icc X (2 * X)) (hδ : δ ∈ Icc 0 (1 / 2))
    (hε : ε ∈ Ioo 0 (1 / 4)) (hσ : 1 < σ) (hσtwo : σ ≤ 2)
    (hlo : 1 ≤ lowerCutoff X A)
    (hs : ∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A) :
    CofactorMainTermBudget.coveredContour X A x δ ε σ s (fun d => (weight d : ℂ)) =
      SignedDivisorErrorDecomposition.smoothedMain s weight ε δ x := by
  rw [contour_eq X A x δ ε σ s (fun d => (weight d : ℂ)) hX hA hx hδ hε
    hσ hσtwo hlo hs]
  unfold SignedDivisorErrorDecomposition.smoothedMain
    SignedDivisorErrorDecomposition.mainTerm HarmanDivisorWindow.reciprocalMass
  push_cast
  ring

theorem smoothing_error (s : Finset ℕ) (weight : ℕ → ℝ) (ε δ x C : ℝ)
    (hs : ∀ d ∈ s, 0 < d) (hx : 0 ≤ x) (hδ : 0 ≤ δ)
    (hclose : ‖mellin (fun y => (Smooth1 smoothing ε y : ℂ)) 1 - 1‖ ≤ C * ε) :
    ‖SignedDivisorErrorDecomposition.smoothedMain s weight ε δ x -
      SignedDivisorErrorDecomposition.mainTerm s weight δ x‖ ≤
        C * ε * (x * δ) *
          SmoothedDirichletKernel.coefficientMass s (fun d => (weight d : ℂ)) 1 := by
  have hmass := CofactorMainTermBudget.reciprocal_sum_norm_le_mass s
    (fun d => (weight d : ℂ)) hs
  have hrecip : ‖(HarmanDivisorWindow.reciprocalMass s weight : ℂ)‖ ≤
      SmoothedDirichletKernel.coefficientMass s (fun d => (weight d : ℂ)) 1 := by
    simpa [HarmanDivisorWindow.reciprocalMass] using hmass
  have hwidth : 0 ≤ x * δ := mul_nonneg hx hδ
  unfold SignedDivisorErrorDecomposition.smoothedMain
  rw [← mul_sub_one, norm_mul]
  unfold SignedDivisorErrorDecomposition.mainTerm
  rw [Complex.ofReal_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hwidth]
  calc
    _ ≤ (x * δ) *
        SmoothedDirichletKernel.coefficientMass s (fun d => (weight d : ℂ)) 1 * (C * ε) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hrecip hwidth) hclose
        (norm_nonneg _) (mul_nonneg hwidth (SmoothedDirichletKernel.mass_nonnegative _ _ _))
    _ = _ := by ring

end FourfoldCofactorMainTerm

#print axioms FourfoldCofactorMainTerm.signed_contour_eq
run_cmd do
  for target in [``FourfoldCofactorMainTerm.contour_eq,
      ``FourfoldCofactorMainTerm.signed_contour_eq,
      ``FourfoldCofactorMainTerm.smoothing_error] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "FOURFOLD COFACTOR MAIN TERM PASSED"
