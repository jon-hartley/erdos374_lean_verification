import QuantitativeFiniteCount

/-!
The quantitative finite-count approximation with a common contour,
smoothing width and truncation height for every cutoff u in [X/2,2X].
This extends QuantitativeFiniteCount to allow subtraction at two cutoffs.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter MeasureTheory Set

namespace UniformFiniteCount
open SmoothedCountBoundary SmoothedDirichletKernel

theorem eventual_approximation : ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
    ∀ (s : Finset ℕ) (weight : ℕ → ℝ) (B : ℕ) (u : ℝ),
      1 ≤ B → (B : ℝ) ≤ X ^ (2 : ℕ) →
      (∀ n ∈ s, 0 < n ∧ n ≤ B) →
      (∀ n ∈ s, 0 ≤ weight n ∧ weight n ≤ X ^ (1 / 200 : ℝ)) →
      u ∈ Icc (X / 2) (2 * X) →
      ‖(sharp s weight u : ℂ) - ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t in Icc (-X) X, integrand s (fun n => (weight n : ℂ))
          MellinSmoothingFunction.smoothing (X ^ (-19 / 20 : ℝ))
          u (1 + 1 / Real.log X) t‖ ≤ X ^ (2 / 25 : ℝ) := by
  obtain ⟨C, hC, happrox⟩ := RapidSmoothedPerron.approximation 20
    MellinSmoothingFunction.smoothing MellinRapidDecay.smoothing_smooth
    MellinSmoothingFunction.support MellinSmoothingFunction.nonnegative
    MellinSmoothingFunction.mass_one
  filter_upwards [RapidPerronParameters.eventual_error (4 * C) (by positivity),
    DirichletCoefficientMass.eventual_bound,
    PolynomialLogEnvelope.eventually_constant_bound 2 (1 / 200)
      (by norm_num) (by norm_num)] with X herr hmass htwo
  refine ⟨herr.1, ?_⟩
  intro s weight B u hB hBX hs hweight hu
  have hXp : 0 < X := (Real.exp_pos 1).trans_le herr.1
  have hup : 0 < u := by linarith [hu.1]
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
  have hW : 2 * X ^ (1 / 200 : ℝ) ≤ X ^ (1 / 100 : ℝ) := by
    calc
      _ ≤ X ^ (1 / 200 : ℝ) * X ^ (1 / 200 : ℝ) :=
        mul_le_mul_of_nonneg_right htwo.2 (by positivity)
      _ = _ := by rw [← Real.rpow_add hXp]; congr 1; norm_num
  have hupow : u ^ (1 + 1 / Real.log X) ≤ 4 * X ^ (1 + 1 / Real.log X) := by
    calc
      _ ≤ (2 * X) ^ (1 + 1 / Real.log X) :=
        Real.rpow_le_rpow hup.le hu.2 (by linarith)
      _ = (2 : ℝ) ^ (1 + 1 / Real.log X) * X ^ (1 + 1 / Real.log X) :=
        Real.mul_rpow (by norm_num) hXp.le
      _ ≤ (2 : ℝ) ^ (2 : ℝ) * X ^ (1 + 1 / Real.log X) :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) hσtwo) (by positivity)
      _ = _ := by norm_num
  have hcount := happrox s weight (X ^ (-19 / 20 : ℝ)) u
    (1 + 1 / Real.log X) X (X ^ (1 / 200 : ℝ)) hup
    (fun n hn => (hs n hn).1) hσ hσtwo hε hXp (by positivity) hweight
  have hfinal := herr.2
    (coefficientMass s (fun n => (weight n : ℂ)) (1 + 1 / Real.log X))
    (2 * X ^ (1 / 200 : ℝ)) (mass_nonnegative _ _ _) hM (by positivity) hW
  apply hcount.trans
  apply le_trans _ hfinal
  apply add_le_add
  · calc
      _ ≤ X ^ (1 / 200 : ℝ) *
          (4 * Real.log 2 * X ^ (-19 / 20 : ℝ) * (2 * X) + 1) := by
        gcongr
        exact hu.2
      _ ≤ (2 * X ^ (1 / 200 : ℝ)) *
          (4 * Real.log 2 * X ^ (-19 / 20 : ℝ) * X + 1) := by
        nlinarith [Real.rpow_pos_of_pos hXp (1 / 200 : ℝ)]
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      _ ≤ 2 * coefficientMass s (fun n => (weight n : ℂ)) (1 + 1 / Real.log X) * C *
          (4 * X ^ (1 + 1 / Real.log X)) :=
        mul_le_mul_of_nonneg_left hupow
          (mul_nonneg (mul_nonneg (by norm_num) (mass_nonnegative _ _ _)) hC.le)
      _ = _ := by ring

end UniformFiniteCount

#print axioms UniformFiniteCount.eventual_approximation
run_cmd do
  let axioms ← Lean.collectAxioms ``UniformFiniteCount.eventual_approximation
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "UNIFORM FINITE COUNT PASSED"
