import UniformFiniteCount
import SmoothedWindowTransfer

/-!
Subtract the uniform approximations at the endpoints of a short window.
The resulting integral is exactly the smoothed transform whose mean
square was bounded earlier, with its required 1/(2*pi) normalization.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter MeasureTheory Set

namespace FiniteWindowApproximation
open SmoothedCountBoundary SmoothedDirichletKernel
open Erdos374.HarmanGram152

theorem integral_difference (s : Finset ℕ) (weight : ℕ → ℝ)
    (ε σ T δ x : ℝ) (hx : 0 < x) (hleft : 0 < x - x * δ)
    (hs : ∀ n ∈ s, 0 < n) (hσ : 1 < σ) (hσtwo : σ ≤ 2)
    (hε : ε ∈ Ioo 0 1) :
    (∫ t in Icc (-T) T, integrand s (fun n => (weight n : ℂ))
      MellinSmoothingFunction.smoothing ε x σ t) -
    (∫ t in Icc (-T) T, integrand s (fun n => (weight n : ℂ))
      MellinSmoothingFunction.smoothing ε (x - x * δ) σ t) =
    SmoothedWindowTransfer.transform (verticalDirichlet152 s (fun n => (weight n : ℂ)) σ)
      MellinSmoothingFunction.smoothing ε (-T) T σ δ x := by
  have hi (u : ℝ) (hu : 0 < u) :=
    integrable_integrand s (fun n => (weight n : ℂ)) MellinSmoothingFunction.smoothing
      ε u σ hu hs hσ hσtwo hε MellinSmoothingFunction.differentiable
      MellinSmoothingFunction.nonnegative MellinSmoothingFunction.support
      MellinSmoothingFunction.mass_one
  rw [← integral_sub (hi x hx).integrableOn (hi (x - x * δ) hleft).integrableOn]
  unfold SmoothedWindowTransfer.transform
  apply integral_congr_ae
  filter_upwards with t
  unfold integrand
  ring

theorem eventual_approximation : ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
    ∀ (s : Finset ℕ) (weight : ℕ → ℝ) (B : ℕ) (x δ : ℝ),
      1 ≤ B → (B : ℝ) ≤ X ^ (2 : ℕ) →
      (∀ n ∈ s, 0 < n ∧ n ≤ B) →
      (∀ n ∈ s, 0 ≤ weight n ∧ weight n ≤ X ^ (1 / 200 : ℝ)) →
      x ∈ Icc X (2 * X) → δ ∈ Icc 0 (1 / 2) →
      ‖((sharp s weight x - sharp s weight (x - x * δ) : ℝ) : ℂ) -
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        SmoothedWindowTransfer.transform
          (verticalDirichlet152 s (fun n => (weight n : ℂ)) (1 + 1 / Real.log X))
          MellinSmoothingFunction.smoothing (X ^ (-19 / 20 : ℝ))
          (-X) X (1 + 1 / Real.log X) δ x‖ ≤ 2 * X ^ (2 / 25 : ℝ) := by
  filter_upwards [UniformFiniteCount.eventual_approximation] with X hX
  refine ⟨hX.1, ?_⟩
  intro s weight B x δ hB hBX hs hweight hx hδ
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hX.1
  have hxp : 0 < x := hXp.trans_le hx.1
  have hleft : x - x * δ ∈ Icc (X / 2) (2 * X) := by
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hδ.2 hxp.le, hx.1]
    · nlinarith [mul_nonneg hxp.le hδ.1, hx.2]
  have hleftp : 0 < x - x * δ := by linarith [hleft.1]
  have hlog : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX.1
  have hσ : 1 < 1 + 1 / Real.log X := by
    have : 0 < 1 / Real.log X := by positivity
    linarith
  have hσtwo : 1 + 1 / Real.log X ≤ 2 := by
    have : 1 / Real.log X ≤ 1 := (div_le_one (by linarith)).mpr hlog
    linarith
  have hε : X ^ (-19 / 20 : ℝ) ∈ Ioo 0 1 :=
    ⟨Real.rpow_pos_of_pos hXp _, Real.rpow_lt_one_of_one_lt_of_neg
      ((Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hX.1) (by norm_num)⟩
  have hxapprox := hX.2 s weight B x hB hBX hs hweight ⟨by linarith [hx.1], hx.2⟩
  have hlapprox := hX.2 s weight B (x - x * δ) hB hBX hs hweight hleft
  rw [← integral_difference s weight _ _ X δ x hxp hleftp
    (fun n hn => (hs n hn).1) hσ hσtwo hε]
  rw [Complex.ofReal_sub, mul_sub]
  rw [sub_sub_sub_comm]
  exact (norm_sub_le _ _).trans (by linarith [add_le_add hxapprox hlapprox])

end FiniteWindowApproximation

#print axioms FiniteWindowApproximation.eventual_approximation
run_cmd do
  let axioms ← Lean.collectAxioms ``FiniteWindowApproximation.eventual_approximation
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "FINITE WINDOW APPROXIMATION PASSED"
