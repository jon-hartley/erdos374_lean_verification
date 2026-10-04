import CompactIntegral

/-!
An integral quadratic-form bound from an explicit symmetric majorant.
This is the continuous version of the finite Gram estimates in the seed.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate

namespace IntegralSchur
open CompactIntegral

theorem double_integral_mono (a b : ℝ) (f g : ℝ → ℝ → ℝ)
    (hf : Continuous f.uncurry) (hg : Continuous g.uncurry)
    (hle : ∀ t u, f t u ≤ g t u) :
    (∫ t in Icc a b, ∫ u in Icc a b, f t u) ≤
      ∫ t in Icc a b, ∫ u in Icc a b, g t u := by
  apply integral_mono
    (continuous_integral a b f hf).integrableOn_Icc
    (continuous_integral a b g hg).integrableOn_Icc
  intro t
  exact integral_mono (by fun_prop : Continuous (f t)).integrableOn_Icc
    (by fun_prop : Continuous (g t)).integrableOn_Icc (hle t)

theorem double_integral_add (a b : ℝ) (f g : ℝ → ℝ → ℝ)
    (hf : Continuous f.uncurry) (hg : Continuous g.uncurry) :
    (∫ t in Icc a b, ∫ u in Icc a b, (f t u + g t u)) =
      (∫ t in Icc a b, ∫ u in Icc a b, f t u) +
        ∫ t in Icc a b, ∫ u in Icc a b, g t u := by
  have hadd : ∀ t, (∫ u in Icc a b, f t u + g t u) =
      (∫ u in Icc a b, f t u) + ∫ u in Icc a b, g t u := by
    intro t
    exact integral_add (by fun_prop : Continuous (f t)).integrableOn_Icc
      (by fun_prop : Continuous (g t)).integrableOn_Icc
  simp_rw [hadd]
  exact integral_add (continuous_integral a b f hf).integrableOn_Icc
    (continuous_integral a b g hg).integrableOn_Icc

theorem quadratic_form_bound (a b R : ℝ) (g : ℝ → ℂ) (H : ℝ → ℝ → ℝ)
    (hg : Continuous g) (hH : Continuous H.uncurry)
    (hHpos : ∀ t u, 0 ≤ H t u) (hHsym : ∀ t u, H t u = H u t)
    (hrow : ∀ t ∈ Icc a b, (∫ u in Icc a b, H t u) ≤ R) :
    (∫ t in Icc a b, ∫ u in Icc a b, ‖g t‖ * ‖g u‖ * H t u) ≤
      R * ∫ t in Icc a b, ‖g t‖ ^ 2 := by
  let F : ℝ → ℝ → ℝ := fun t u => ‖g t‖ * ‖g u‖ * H t u
  let G : ℝ → ℝ → ℝ := fun t u => ‖g t‖ ^ 2 * H t u
  have hF : Continuous F.uncurry := by dsimp [F]; fun_prop
  have hG : Continuous G.uncurry := by dsimp [G]; fun_prop
  have hGswap : Continuous (fun p : ℝ × ℝ => G p.2 p.1) := by fun_prop
  have htwo : 2 * (∫ t in Icc a b, ∫ u in Icc a b, F t u) ≤
      2 * (∫ t in Icc a b, ∫ u in Icc a b, G t u) := by
    calc
      _ = ∫ t in Icc a b, ∫ u in Icc a b, 2 * F t u := by
        simp_rw [integral_const_mul]
      _ ≤ ∫ t in Icc a b, ∫ u in Icc a b, (G t u + G u t) := by
        apply double_integral_mono a b _ _ (by fun_prop) (by fun_prop)
        intro t u
        dsimp [F, G]
        rw [hHsym u t]
        have hh := mul_le_mul_of_nonneg_right
          (show 2 * ‖g t‖ * ‖g u‖ ≤ ‖g t‖ ^ 2 + ‖g u‖ ^ 2 by
            nlinarith [sq_nonneg (‖g t‖ - ‖g u‖)]) (hHpos t u)
        nlinarith only [hh]
      _ = (∫ t in Icc a b, ∫ u in Icc a b, G t u) +
          ∫ t in Icc a b, ∫ u in Icc a b, G u t :=
        double_integral_add a b G (fun t u => G u t) hG hGswap
      _ = _ := by rw [integral_swap a b a b G hG]; ring
  have hrowBound : (∫ t in Icc a b, ∫ u in Icc a b, G t u) ≤
      R * ∫ t in Icc a b, ‖g t‖ ^ 2 := by
    dsimp [G]
    simp_rw [integral_const_mul]
    rw [← integral_const_mul]
    apply setIntegral_mono_on
      (by
        exact ((by fun_prop : Continuous (fun t => ‖g t‖ ^ 2)).mul
          (continuous_integral a b H hH)).integrableOn_Icc)
      (by fun_prop : Continuous (fun t => R * ‖g t‖ ^ 2)).integrableOn_Icc
      measurableSet_Icc
    intro t ht
    have hh := mul_le_mul_of_nonneg_left (hrow t ht) (sq_nonneg ‖g t‖)
    nlinarith only [hh]
  linarith

end IntegralSchur

#print axioms IntegralSchur.quadratic_form_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``IntegralSchur.quadratic_form_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "INTEGRAL SCHUR PASSED"
