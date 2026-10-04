import IntegralSchur

/-!
Turn a proved row-integral bound for the actual correlation kernel into
a mean-square bound for the associated compact integral transform.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate

namespace IntegralTransformBound
open CompactIntegral IntegralSchur

theorem mean_square_le (a b c d R : ℝ)
    (K : ℝ → ℝ → ℂ) (g : ℝ → ℂ) (H : ℝ → ℝ → ℝ)
    (hK : Continuous K.uncurry) (hg : Continuous g)
    (hH : Continuous H.uncurry) (hHpos : ∀ t u, 0 ≤ H t u)
    (hHsym : ∀ t u, H t u = H u t)
    (hkernel : ∀ t u, ‖correlation K c d t u‖ ≤ H t u)
    (hrow : ∀ t ∈ Icc a b, (∫ u in Icc a b, H t u) ≤ R) :
    (∫ x in Icc c d, ‖transform K g a b x‖ ^ 2) ≤
      R * ∫ t in Icc a b, ‖g t‖ ^ 2 := by
  let Z : ℝ → ℝ → ℂ := fun t u => g t * conj (g u) * correlation K c d t u
  have hcorr := continuous_correlation K c d hK
  have hZ : Continuous Z.uncurry := by dsimp [Z]; fun_prop
  have hnormZ : Continuous (fun p : ℝ × ℝ => ‖Z p.1 p.2‖) := hZ.norm
  have hnonneg : 0 ≤ ∫ x in Icc c d, ‖transform K g a b x‖ ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  have heq := congrArg norm (mean_square_expansion K g a b c d hK hg)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg] at heq
  calc
    _ = ‖∫ t in Icc a b, ∫ u in Icc a b, Z t u‖ := heq
    _ ≤ ∫ t in Icc a b, ‖∫ u in Icc a b, Z t u‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t in Icc a b, ∫ u in Icc a b, ‖Z t u‖ := by
      apply integral_mono
        (continuous_integral a b Z hZ).norm.integrableOn_Icc
        (continuous_integral a b (fun t u => ‖Z t u‖) hnormZ).integrableOn_Icc
      intro t
      exact norm_integral_le_integral_norm _
    _ ≤ ∫ t in Icc a b, ∫ u in Icc a b, ‖g t‖ * ‖g u‖ * H t u := by
      apply double_integral_mono a b (fun t u => ‖Z t u‖)
        (fun t u => ‖g t‖ * ‖g u‖ * H t u) hnormZ (by fun_prop)
      intro t u
      dsimp [Z]
      simp only [norm_mul, RCLike.norm_conj]
      exact mul_le_mul_of_nonneg_left (hkernel t u) (by positivity)
    _ ≤ _ := quadratic_form_bound a b R g H hg hH hHpos hHsym hrow

end IntegralTransformBound

#print axioms IntegralTransformBound.mean_square_le
run_cmd do
  let axioms ← Lean.collectAxioms ``IntegralTransformBound.mean_square_le
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "INTEGRAL TRANSFORM BOUND PASSED"
