import FiniteWindowApproximation
import CompactIntegralSplit

/-!
Split the actual finite-counting contour into low, positive-high and
negative-high frequency pieces. The compact pieces share endpoints
only on null sets. No cancellation estimate is assumed or concluded.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set

namespace FiniteWindowFrequencySplit
open SmoothedWindowTransfer SmoothedDirichletKernel
open Erdos374.HarmanGram152

theorem integrable_kernel (s : Finset ℕ) (weight : ℕ → ℝ)
    (ε σ δ x : ℝ) (hx : 0 < x) (hleft : 0 < x - x * δ)
    (hs : ∀ n ∈ s, 0 < n) (hσ : 1 < σ) (hσtwo : σ ≤ 2)
    (hε : ε ∈ Ioo 0 1) :
    Integrable (fun t => verticalDirichlet152 s (fun n => (weight n : ℂ)) σ t *
      mellin (fun u => (Smooth1 MellinSmoothingFunction.smoothing ε u : ℂ))
        (MellinWindowFactor.line σ t) *
      ((x : ℂ) ^ MellinWindowFactor.line σ t -
        ((x - x * δ : ℝ) : ℂ) ^ MellinWindowFactor.line σ t)) := by
  have hi (u : ℝ) (hu : 0 < u) :=
    integrable_integrand s (fun n => (weight n : ℂ)) MellinSmoothingFunction.smoothing
      ε u σ hu hs hσ hσtwo hε MellinSmoothingFunction.differentiable
      MellinSmoothingFunction.nonnegative MellinSmoothingFunction.support
      MellinSmoothingFunction.mass_one
  apply ((hi x hx).sub (hi (x - x * δ) hleft)).congr
  filter_upwards with t
  simp only [Pi.sub_apply]
  unfold integrand
  ring

theorem split (s : Finset ℕ) (weight : ℕ → ℝ) (ε σ δ x a b c : ℝ)
    (hx : 0 < x) (hleft : 0 < x - x * δ)
    (hs : ∀ n ∈ s, 0 < n) (hσ : 1 < σ) (hσtwo : σ ≤ 2)
    (hε : ε ∈ Ioo 0 1) (hab : a ≤ b) (hbc : b ≤ c) :
    transform (verticalDirichlet152 s (fun n => (weight n : ℂ)) σ)
      MellinSmoothingFunction.smoothing ε a c σ δ x =
    transform (verticalDirichlet152 s (fun n => (weight n : ℂ)) σ)
      MellinSmoothingFunction.smoothing ε a b σ δ x +
    transform (verticalDirichlet152 s (fun n => (weight n : ℂ)) σ)
      MellinSmoothingFunction.smoothing ε b c σ δ x :=
  CompactIntegralSplit.split _ a b c hab hbc
    (integrable_kernel s weight ε σ δ x hx hleft hs hσ hσtwo hε).integrableOn

theorem three_bands (s : Finset ℕ) (weight : ℕ → ℝ) (ε σ δ x T H : ℝ)
    (hx : 0 < x) (hleft : 0 < x - x * δ)
    (hs : ∀ n ∈ s, 0 < n) (hσ : 1 < σ) (hσtwo : σ ≤ 2)
    (hε : ε ∈ Ioo 0 1) (hH : 0 ≤ H) (hHT : H ≤ T) :
    transform (verticalDirichlet152 s (fun n => (weight n : ℂ)) σ)
      MellinSmoothingFunction.smoothing ε (-T) T σ δ x =
    transform (verticalDirichlet152 s (fun n => (weight n : ℂ)) σ)
      MellinSmoothingFunction.smoothing ε (-T) (-H) σ δ x +
    transform (verticalDirichlet152 s (fun n => (weight n : ℂ)) σ)
      MellinSmoothingFunction.smoothing ε (-H) H σ δ x +
    transform (verticalDirichlet152 s (fun n => (weight n : ℂ)) σ)
      MellinSmoothingFunction.smoothing ε H T σ δ x := by
  rw [split s weight ε σ δ x (-T) H T hx hleft hs hσ hσtwo hε (by linarith) hHT]
  rw [split s weight ε σ δ x (-T) (-H) H hx hleft hs hσ hσtwo hε
    (by linarith) (by linarith)]

end FiniteWindowFrequencySplit

#print axioms FiniteWindowFrequencySplit.three_bands
run_cmd do
  let axioms ← Lean.collectAxioms ``FiniteWindowFrequencySplit.three_bands
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "FINITE WINDOW FREQUENCY SPLIT PASSED"
