import SupremumMoment

/-!
Choose the amplitude cutoff so that the inverse-sixth-power tail
contributes exactly a prescribed positive budget. This is the algebraic
form needed to apply the moment bound with a supremum power saving.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace MomentThreshold
open DirichletLargeValueMeasure SupremumMoment

theorem supremum_bound (F : ℝ → ℂ) (a T v U p A B : ℝ)
    (hF : Continuous F) (hv : 0 < v) (hU : 0 ≤ U)
    (hp : 2 ≤ p) (hp6 : p ≤ 6) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcap : ∀ t ∈ Icc a (a + T), ‖F t‖ ≤ U)
    (hlevel : ∀ w : ℝ, 0 < w → volume (levelSet F a T w) ≤
      ENNReal.ofReal (A / w ^ 2 + B / w ^ 6)) :
    (∫ t in Icc a (a + T), ‖F t‖ ^ p) ≤
      v ^ (p - 2) * (∫ t in Icc a (a + T), ‖F t‖ ^ 2) +
        bandCountBound v U * (2 : ℝ) ^ p *
          (A * (2 * U) ^ (p - 2) + B * v ^ (p - 6)) := by
  by_cases hsmall : U ≤ v
  · have hh := DyadicMoment.integral_bound F a T v p 0 hF hv hp
      (fun t ht => by simpa using (hcap t ht).trans hsmall)
    simp only [Finset.range_zero, Finset.sum_empty, add_zero] at hh
    apply hh.trans
    apply le_add_of_nonneg_right
    exact mul_nonneg (mul_nonneg (bandCountBound_nonneg v U) (by positivity)) (by positivity)
  · have hh := SupremumMoment.integral_bound F a T v U p A B
      hF hv hp hp6 hA hB hcap hlevel
    simpa only [max_eq_left (le_of_not_ge hsmall)] using hh

def cutoff (B μ p : ℝ) : ℝ := (B / μ) ^ (1 / (6 - p))

theorem cutoff_positive (B μ p : ℝ) (hB : 0 < B) (hμ : 0 < μ) :
    0 < cutoff B μ p := by
  unfold cutoff
  positivity

theorem cutoff_tail (B μ p : ℝ) (hB : 0 < B) (hμ : 0 < μ) (hp : p < 6) :
    B * cutoff B μ p ^ (p - 6) = μ := by
  unfold cutoff
  rw [← Real.rpow_mul (div_pos hB hμ).le]
  have he : 1 / (6 - p) * (p - 6) = -1 := by
    have hd : 6 - p ≠ 0 := ne_of_gt (by linarith)
    field_simp [hd]
    ring
  rw [he, Real.rpow_neg_one]
  field_simp

theorem cutoff_small_power (B μ p : ℝ) (hB : 0 < B) (hμ : 0 < μ) :
    cutoff B μ p ^ (p - 2) = (B / μ) ^ ((p - 2) / (6 - p)) := by
  unfold cutoff
  rw [← Real.rpow_mul (div_pos hB hμ).le]
  congr 1
  ring

theorem integral_bound (F : ℝ → ℂ) (a T U p A B μ : ℝ)
    (hF : Continuous F) (hU : 0 ≤ U) (hp : 2 ≤ p) (hp6 : p < 6)
    (hA : 0 ≤ A) (hB : 0 < B) (hμ : 0 < μ)
    (hcap : ∀ t ∈ Icc a (a + T), ‖F t‖ ≤ U)
    (hpower : U ^ (p - 2) ≤ μ)
    (hlevel : ∀ w : ℝ, 0 < w → volume (levelSet F a T w) ≤
      ENNReal.ofReal (A / w ^ 2 + B / w ^ 6)) :
    (∫ t in Icc a (a + T), ‖F t‖ ^ p) ≤
      (B / μ) ^ ((p - 2) / (6 - p)) * (∫ t in Icc a (a + T), ‖F t‖ ^ 2) +
        bandCountBound (cutoff B μ p) U * (2 : ℝ) ^ p *
          (A * (2 : ℝ) ^ (p - 2) + 1) * μ := by
  have hh := supremum_bound F a T (cutoff B μ p) U p A B hF
    (cutoff_positive B μ p hB hμ) hU hp hp6.le hA hB.le hcap hlevel
  rw [cutoff_tail B μ p hB hμ hp6, cutoff_small_power B μ p hB hμ] at hh
  apply hh.trans
  apply add_le_add le_rfl
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hU]
  have hterm : A * ((2 : ℝ) ^ (p - 2) * U ^ (p - 2)) + μ ≤
      (A * (2 : ℝ) ^ (p - 2) + 1) * μ := by
    have hh := mul_le_mul_of_nonneg_left hpower
      (mul_nonneg hA (by positivity : 0 ≤ (2 : ℝ) ^ (p - 2)))
    nlinarith
  have hfactor : 0 ≤ bandCountBound (cutoff B μ p) U * (2 : ℝ) ^ p :=
    mul_nonneg (bandCountBound_nonneg _ _) (by positivity)
  exact (mul_le_mul_of_nonneg_left hterm hfactor).trans_eq (by ring)

end MomentThreshold

#print axioms MomentThreshold.integral_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``MomentThreshold.integral_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "MOMENT THRESHOLD PASSED"
