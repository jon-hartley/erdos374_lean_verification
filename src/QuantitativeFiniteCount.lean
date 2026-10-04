import RapidPerronParameters
import DirichletCoefficientMass

/-!
An actual sharp finite count is approximated by a truncated smoothed
Mellin integral with error at most X^(2/25). The positive integer
support lies below X^2, and each nonnegative weight is at most
X^(1/200). This is a counting identity with a small error, not a
prime main term. It composes the rapid Perron and harmonic bounds.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter MeasureTheory Set

namespace QuantitativeFiniteCount
open SmoothedCountBoundary SmoothedDirichletKernel

theorem eventual_approximation : ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
    ∀ (s : Finset ℕ) (weight : ℕ → ℝ) (B : ℕ),
      1 ≤ B → (B : ℝ) ≤ X ^ (2 : ℕ) →
      (∀ n ∈ s, 0 < n ∧ n ≤ B) →
      (∀ n ∈ s, 0 ≤ weight n ∧ weight n ≤ X ^ (1 / 200 : ℝ)) →
      ‖(sharp s weight X : ℂ) - ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t in Icc (-X) X, integrand s (fun n => (weight n : ℂ))
          MellinSmoothingFunction.smoothing (X ^ (-19 / 20 : ℝ))
          X (1 + 1 / Real.log X) t‖ ≤ X ^ (2 / 25 : ℝ) := by
  obtain ⟨C, hC, happrox⟩ := RapidSmoothedPerron.approximation 20
    MellinSmoothingFunction.smoothing MellinRapidDecay.smoothing_smooth
    MellinSmoothingFunction.support MellinSmoothingFunction.nonnegative
    MellinSmoothingFunction.mass_one
  filter_upwards [RapidPerronParameters.eventual_error C hC,
    DirichletCoefficientMass.eventual_bound] with X herr hmass
  refine ⟨herr.1, ?_⟩
  intro s weight B hB hBX hs hweight
  have hXp : 0 < X := (Real.exp_pos 1).trans_le herr.1
  have hlog : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) herr.1
  have hXone : 1 < X := (Real.one_lt_exp_iff.mpr (by norm_num)).trans_le herr.1
  have hσ : 1 < 1 + 1 / Real.log X := by
    have : 0 < 1 / Real.log X := by positivity
    linarith
  have hσtwo : 1 + 1 / Real.log X ≤ 2 := by
    have : 1 / Real.log X ≤ 1 := (div_le_one (by linarith)).mpr hlog
    linarith
  have hε : X ^ (-19 / 20 : ℝ) ∈ Ioo 0 1 :=
    ⟨Real.rpow_pos_of_pos hXp _, Real.rpow_lt_one_of_one_lt_of_neg hXone (by norm_num)⟩
  have hcoeff : ∀ n ∈ s, ‖(weight n : ℂ)‖ ≤ X ^ (1 / 200 : ℝ) := by
    intro n hn
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hweight n hn).1]
      using (hweight n hn).2
  have hM := hmass.2 s (fun n => (weight n : ℂ)) B (1 + 1 / Real.log X)
    hB hBX hs hσ.le hcoeff
  have hW : X ^ (1 / 200 : ℝ) ≤ X ^ (1 / 100 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hmass.1 (by norm_num)
  have hcount := happrox s weight (X ^ (-19 / 20 : ℝ)) X
    (1 + 1 / Real.log X) X (X ^ (1 / 200 : ℝ)) hXp
    (fun n hn => (hs n hn).1) hσ hσtwo hε hXp (by positivity) hweight
  apply hcount.trans
  simpa only [Nat.reduceAdd, Nat.cast_ofNat] using
    herr.2 (coefficientMass s (fun n => (weight n : ℂ)) (1 + 1 / Real.log X))
      (X ^ (1 / 200 : ℝ)) (mass_nonnegative _ _ _) hM (by positivity) hW

end QuantitativeFiniteCount

#print axioms QuantitativeFiniteCount.eventual_approximation
run_cmd do
  let axioms ← Lean.collectAxioms ``QuantitativeFiniteCount.eventual_approximation
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "QUANTITATIVE FINITE COUNT PASSED"
