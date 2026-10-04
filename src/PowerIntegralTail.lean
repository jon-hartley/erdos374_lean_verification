import IntegralTail

/-!
Truncation with a general inverse-power tail. The derivative order in
the smoothing estimate can be selected before the spatial scale.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set

namespace PowerIntegralTail

theorem positive_tail (g : ℝ → ℂ) (A T p : ℝ) (hT : 0 < T) (hp : 1 < p)
    (hbound : ∀ t, T < t → ‖g t‖ ≤ A * t ^ (-p)) :
    ‖∫ t in Ioi T, g t‖ ≤ A * T ^ (1 - p) / (p - 1) := by
  have hint : IntegrableOn (fun t : ℝ => A * t ^ (-p)) (Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -p < -1) hT).const_mul A
  calc
    _ ≤ ∫ t in Ioi T, ‖g t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi T, A * t ^ (-p) := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hint
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hbound t ht
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hT,
        show -p + 1 = 1 - p by ring,
        show 1 - p = -(p - 1) by ring]
      simp only [div_neg, neg_div, neg_neg]
      ring

theorem symmetric_truncation (g : ℝ → ℂ) (A T p : ℝ) (hT : 0 < T) (hp : 1 < p)
    (hg : Integrable g) (hbound : ∀ t, T < |t| → ‖g t‖ ≤ A * |t| ^ (-p)) :
    ‖(∫ t : ℝ, g t) - ∫ t in Icc (-T) T, g t‖ ≤
      2 * A * T ^ (1 - p) / (p - 1) := by
  have hpositive := positive_tail g A T p hT hp (by
    intro t ht
    simpa only [abs_of_pos (hT.trans ht)] using hbound t
      (by rwa [abs_of_pos (hT.trans ht)]))
  have hnegative := positive_tail (fun t => g (-t)) A T p hT hp (by
    intro t ht
    simpa only [abs_neg, abs_of_pos (hT.trans ht)] using
      hbound (-t) (by simpa only [abs_neg, abs_of_pos (hT.trans ht)] using ht))
  rw [integral_comp_neg_Ioi, integral_Iic_eq_integral_Iio] at hnegative
  have hcompl : (Icc (-T) T)ᶜ = Iio (-T) ∪ Ioi T := by
    ext t
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le, mem_union, mem_Iio, mem_Ioi]
  rw [← setIntegral_compl measurableSet_Icc hg, hcompl,
    setIntegral_union (by
      apply Set.disjoint_left.mpr
      intro t hl hr
      have hl' : t < -T := hl
      have hr' : T < t := hr
      linarith)
      measurableSet_Ioi hg.integrableOn hg.integrableOn]
  exact (norm_add_le _ _).trans ((add_le_add hnegative hpositive).trans_eq (by ring))

end PowerIntegralTail

#print axioms PowerIntegralTail.symmetric_truncation
run_cmd do
  let axioms ← Lean.collectAxioms ``PowerIntegralTail.symmetric_truncation
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "POWER INTEGRAL TAIL PASSED"
