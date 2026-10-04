import FiniteMellinInversion

/-!
An explicit truncation bound for an absolutely integrable complex
frequency function whose tails are at most A/t^2. This lemma does not
presume the decay bound for any particular arithmetic function.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set

namespace IntegralTail

theorem positive_tail (g : ℝ → ℂ) (A T : ℝ) (hT : 0 < T)
    (hbound : ∀ t, T < t → ‖g t‖ ≤ A / t ^ 2) :
    ‖∫ t in Ioi T, g t‖ ≤ A / T := by
  have hpower : (fun t : ℝ => A / t ^ 2) = fun t => A * t ^ (-2 : ℝ) := by
    funext t
    norm_num [Real.rpow_neg_natCast, div_eq_mul_inv]
  have hint : IntegrableOn (fun t : ℝ => A / t ^ 2) (Ioi T) := by
    rw [hpower]
    exact (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT).const_mul A
  calc
    _ ≤ ∫ t in Ioi T, ‖g t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi T, A / t ^ 2 := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hint
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hbound t ht
    _ = A / T := by
      rw [hpower, integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hT]
      norm_num [Real.rpow_neg_one]
      ring

theorem symmetric_truncation (g : ℝ → ℂ) (A T : ℝ) (hT : 0 < T)
    (hg : Integrable g)
    (hbound : ∀ t, T < |t| → ‖g t‖ ≤ A / t ^ 2) :
    ‖(∫ t : ℝ, g t) - ∫ t in Icc (-T) T, g t‖ ≤ 2 * A / T := by
  have hp := positive_tail g A T hT (by
    intro t ht
    apply hbound
    rwa [abs_of_pos (hT.trans ht)])
  have hn := positive_tail (fun t => g (-t)) A T hT (by
    intro t ht
    simpa only [abs_neg, abs_of_pos (hT.trans ht), neg_sq] using
      hbound (-t) (by simpa only [abs_neg, abs_of_pos (hT.trans ht)] using ht))
  rw [integral_comp_neg_Ioi, integral_Iic_eq_integral_Iio] at hn
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
  exact (norm_add_le _ _).trans ((add_le_add hn hp).trans_eq (by ring))

end IntegralTail

#print axioms IntegralTail.symmetric_truncation
run_cmd do
  let axioms ← Lean.collectAxioms ``IntegralTail.symmetric_truncation
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "INTEGRAL TAIL PASSED"
