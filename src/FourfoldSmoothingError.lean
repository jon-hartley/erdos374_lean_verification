import FourfoldCofactorMainTerm
import FourfoldCoefficientMass
import PolynomialLogEnvelope

/-! Power saving for the smoothing multiplier of the actual signed main term. -/

set_option autoImplicit false
noncomputable section
open Filter MeasureTheory Set

namespace FourfoldSmoothingError
open SignedDivisorErrorDecomposition

theorem eventually_bound : ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
    X ^ (-19 / 20 : ℝ) ∈ Ioo 0 (1 / 4) ∧
    ∀ (A x Y : ℝ) (s : Finset ℕ) (weight : ℕ → ℝ),
      1 ≤ A →
      (∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A) →
      (∀ d ∈ s, |weight d| ≤ X ^ (1 / 20 : ℝ)) →
      x ∈ Icc X (2 * X) → 0 ≤ Y →
      ‖smoothedMain s weight (X ^ (-19 / 20 : ℝ)) (Y / X) x -
        mainTerm s weight (Y / X) x‖ ≤ Y * X ^ (-1 / 2 : ℝ) := by
  obtain ⟨C, hC, ε₀, hε₀, hclose⟩ := CofactorMainTermBudget.multiplier_close
  have hsmall := (tendsto_rpow_neg_atTop
    (by norm_num : (0 : ℝ) < 19 / 20)).eventually
      (gt_mem_nhds (lt_min hε₀ (by norm_num : (0 : ℝ) < 1 / 4)))
  filter_upwards [hsmall, PolynomialLogEnvelope.eventually_constant_bound
    (8 * C) (2 / 5) (by positivity) (by norm_num)] with X hsmall hc
  have hXp : 0 < X := by linarith [hc.1]
  have hεpos : 0 < X ^ (-19 / 20 : ℝ) := Real.rpow_pos_of_pos hXp _
  have hεsmall : X ^ (-19 / 20 : ℝ) < min ε₀ (1 / 4) := by
    simpa only [neg_div] using hsmall
  refine ⟨hc.1, ⟨hεpos, hεsmall.trans_le (min_le_right _ _)⟩, ?_⟩
  intro A x Y s weight hA hs hw hx hY
  have hpos : ∀ d ∈ s, 0 < d := by
    intro d hd
    have hh : (0 : ℝ) < d := by linarith [(hs d hd).1]
    exact_mod_cast hh
  have hm := FourfoldCoefficientMass.real_weight_mass_bound s A
    (X ^ (1 / 20 : ℝ)) 1 weight hA (by positivity) (by norm_num) hs hw
  have hmassnonneg := SmoothedDirichletKernel.mass_nonnegative s
    (fun d => (weight d : ℂ)) 1
  have hb := FourfoldCofactorMainTerm.smoothing_error s weight
    (X ^ (-19 / 20 : ℝ)) (Y / X) x C hpos
    (hXp.le.trans hx.1) (div_nonneg hY hXp.le)
    (hclose _ hεpos (hεsmall.trans_le (min_le_left _ _)))
  have hwidth : x * (Y / X) ≤ 2 * Y := by
    calc
      _ ≤ (2 * X) * (Y / X) :=
        mul_le_mul_of_nonneg_right hx.2 (by positivity)
      _ = _ := by field_simp
  apply hb.trans
  calc
    _ ≤ C * X ^ (-19 / 20 : ℝ) * (2 * Y) *
        (4 * X ^ (1 / 20 : ℝ)) := by gcongr
    _ = Y * (8 * C) * X ^ (-9 / 10 : ℝ) := by
      rw [show Y * (8 * C) * X ^ (-9 / 10 : ℝ) =
        Y * (8 * C) * (X ^ (-19 / 20 : ℝ) * X ^ (1 / 20 : ℝ)) by
          rw [← Real.rpow_add hXp]; norm_num]
      ring
    _ ≤ Y * X ^ (2 / 5 : ℝ) * X ^ (-9 / 10 : ℝ) := by gcongr; exact hc.2
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hXp]; norm_num

end FourfoldSmoothingError

#print axioms FourfoldSmoothingError.eventually_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``FourfoldSmoothingError.eventually_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "FOURFOLD SMOOTHING ERROR PASSED"
