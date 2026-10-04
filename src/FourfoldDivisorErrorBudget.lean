import SignedDivisorMixedBudget
import FourfoldDivisorApproximation
import FourfoldCofactorError
import FourfoldContinuousTruncation
import FourfoldSmoothingError
import FourfoldDivisorUpperTail

/-!
All errors except the two middle-frequency bands are discharged for the
same actual signed count and common cofactor endpoints. The remaining
middle-band input is displayed as a squared-mean bound on that exact
contour, ready for the factored coefficient theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section
open Filter MeasureTheory Set

namespace FourfoldDivisorErrorBudget
open MellinCofactorCoverage HarmanDivisorWindow HarmanDivisorContour
open SignedDivisorErrorDecomposition

def coefficientExponent (ell η κ : ℝ) : ℝ :=
  min (1 / 1600) (min (ell / 16) (min (η / 4) (κ / 384)))

theorem coefficientExponent_pos (ell η κ : ℝ)
    (hell : 0 < ell) (hη : 0 < η) (hκ : 0 < κ) :
    0 < coefficientExponent ell η κ := by
  unfold coefficientExponent
  positivity

theorem eventually_bound (θ ell η κ : ℝ) (hθ : 2 / 25 < θ)
    (hell : 0 < ell) (hη : 0 < η) (hκ : 0 < κ) :
    ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
      ∀ (A Y H U middle : ℝ) (s : Finset ℕ) (weight : ℕ → ℝ),
        1 ≤ A → A ≤ X →
        (∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A) →
        (∀ d ∈ s, |weight d| ≤ X ^ coefficientExponent ell η κ) →
        X ^ ell ≤ (lowerCutoff X A : ℝ) →
        X ^ η ≤ H → H ≤ (lowerCutoff X A : ℝ) ^ (1 / 4 : ℝ) →
        H ≤ U → U ≤ X → X ^ (1 - θ + κ) ≤ U →
        X ^ θ ≤ Y → Y ≤ X / 2 →
        ((1 / X) * (∫ x in Icc X (2 * X),
          ‖productTransform s weight (lowerCutoff X A) (upperCutoff X A)
            (X ^ (-19 / 20 : ℝ)) (-U) (-H)
              (1 + 1 / Real.log X) (Y / X) x‖ ^ 2) ≤ middle) →
        ((1 / X) * (∫ x in Icc X (2 * X),
          ‖productTransform s weight (lowerCutoff X A) (upperCutoff X A)
            (X ^ (-19 / 20 : ℝ)) H U
              (1 + 1 / Real.log X) (Y / X) x‖ ^ 2) ≤ middle) →
        (1 / X) * (∫ x in Icc X (2 * X),
          remainder s weight (x - x * (Y / X)) x ^ 2) ≤
            8 * ((Y * X ^ (-((θ - 2 / 25) / 2))) ^ 2 +
              (Y * X ^ (-ell / 4)) ^ 2 + (Y * X ^ (-η / 2)) ^ 2 +
              (Y * X ^ (-1 / 2 : ℝ)) ^ 2 + 2 * middle +
              2 * (Y ^ 2 * X ^ (-κ))) := by
  filter_upwards [FourfoldDivisorApproximation.eventually_relative θ hθ,
    FourfoldCofactorError.eventually_common_cofactor ell hell,
    FourfoldContinuousTruncation.eventually_power_bound η hη,
    FourfoldSmoothingError.eventually_bound,
    FourfoldDivisorUpperTail.eventual_tail θ κ hκ,
    FourfoldDivisorUpperTail.eventual_negative_tail θ κ hκ]
      with X hsharp hlow htrunc hsmooth huppos hupneg
  refine ⟨hsharp.1, ?_⟩
  intro A Y H U middle s weight hA hAX hs hw hlo hH hHK hHU hUX hU hY hYX
    hmidneg hmidpos
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hsharp.1
  have hXone : 1 ≤ X := hsmooth.1
  have hAp : 0 < A := by linarith
  have hYpos : 0 ≤ Y := (Real.rpow_pos_of_pos hXp θ).le.trans hY
  have hYlt : Y < X := by linarith
  have hεquarter : X ^ (-19 / 20 : ℝ) ∈ Ioo 0 (1 / 4) := hsmooth.2.1
  have hε : X ^ (-19 / 20 : ℝ) ∈ Ioo 0 1 := by
    constructor <;> linarith [hεquarter.1, hεquarter.2]
  have hδ : Y / X ∈ Icc (0 : ℝ) (1 / 2) := by
    refine ⟨div_nonneg hYpos hXp.le, ?_⟩
    apply (div_le_iff₀ hXp).mpr
    linarith
  have hδone : Y / X ∈ Ico (0 : ℝ) 1 := ⟨hδ.1, by linarith [hδ.2]⟩
  have hHone : 1 ≤ H := (Real.one_le_rpow hXone hη.le).trans hH
  have hloOne : 1 ≤ lowerCutoff X A := by
    exact_mod_cast (Real.one_le_rpow hXone hell.le).trans hlo
  have hhi : 0 < upperCutoff X A := by
    have hh := cutoff_strict X A hXp hAp
    omega
  have hpos : ∀ d ∈ s, 0 < d := by
    intro d hd
    exact_mod_cast hAp.trans (hs d hd).1
  have hlog : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hsharp.1
  have hσ : 1 < 1 + 1 / Real.log X := by
    have hh : 0 < 1 / Real.log X := by positivity
    linarith
  have hcap (a : ℝ) (ha : coefficientExponent ell η κ ≤ a) :
      ∀ d ∈ s, |weight d| ≤ X ^ a := by
    intro d hd
    exact (hw d hd).trans (Real.rpow_le_rpow_of_exponent_le hXone ha)
  have hsharpCap := hcap (1 / 1600) (min_le_left _ _)
  have hlowCap := hcap (ell / 16)
    ((min_le_right _ _).trans (min_le_left _ _))
  have htruncCap := hcap (η / 4)
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hupperCap := hcap (κ / 384)
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hsmoothCap := hcap (1 / 20)
    ((min_le_left _ _).trans (by norm_num))
  apply SignedDivisorMixedBudget.bound s weight (lowerCutoff X A)
    (upperCutoff X A) (X ^ (-19 / 20 : ℝ)) X U H (1 + 1 / Real.log X)
    (Y / X) (Y * X ^ (-((θ - 2 / 25) / 2))) (Y * X ^ (-ell / 4))
    (Y * X ^ (-η / 2)) (Y * X ^ (-1 / 2 : ℝ)) middle (Y ^ 2 * X ^ (-κ))
    hpos (by omega) hhi hXp hε hσ hδone (by linarith) hHU hUX
  · intro x hx
    exact hsharp.2 A x (Y / X) Y s weight hA hAX hs hsharpCap hx hδ hY
  · intro x hx
    exact hlow.2 A s weight (X ^ (-19 / 20 : ℝ)) x Y H hA hs hlowCap hlo
      hε hx hYpos hYlt hHone hHK
  · intro x hx
    simpa only [neg_div] using
      htrunc.2 A x Y (X ^ (-19 / 20 : ℝ)) H s weight hA hloOne hs
        htruncCap hx hYpos hYX hεquarter hH
  · intro x hx
    exact hsmooth.2.2 A x Y s weight hA hs hsmoothCap hx hYpos
  · exact hmidneg
  · exact hmidpos
  · exact hupneg.2 A Y (X ^ (-19 / 20 : ℝ)) U s weight hA hAX hs hupperCap
      hY hYlt hε hU hUX
  · exact huppos.2 A Y (X ^ (-19 / 20 : ℝ)) U s weight hA hAX hs hupperCap
      hY hYlt hε hU hUX

end FourfoldDivisorErrorBudget

#print axioms FourfoldDivisorErrorBudget.eventually_bound
run_cmd do
  for target in [``FourfoldDivisorErrorBudget.coefficientExponent_pos,
      ``FourfoldDivisorErrorBudget.eventually_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "FOURFOLD DIVISOR ERROR BUDGET PASSED"
