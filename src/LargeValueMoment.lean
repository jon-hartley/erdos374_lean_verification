import DyadicMoment

/-!
Moments between orders two and six from explicit V^(-2) and V^(-6)
level-measure bounds. The finite dyadic covering count remains explicit.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LargeValueMoment
open DirichletLargeValueMeasure

theorem level_term_algebra (w p A B : ℝ) (hw : 0 < w) :
    (2 * w) ^ p * (A / w ^ 2 + B / w ^ 6) =
      (2 : ℝ) ^ p * (A * w ^ (p - 2) + B * w ^ (p - 6)) := by
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hw.le,
    Real.rpow_sub hw, Real.rpow_sub hw, Real.rpow_two,
    show w ^ (6 : ℝ) = w ^ (6 : ℕ) by norm_num]
  ring

theorem integral_bound (F : ℝ → ℂ) (a T v p A B : ℝ) (J : ℕ)
    (hF : Continuous F) (hv : 0 < v) (hp : 2 ≤ p) (hp6 : p ≤ 6)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcap : ∀ t ∈ Icc a (a + T), ‖F t‖ ≤ (2 : ℝ) ^ J * v)
    (hlevel : ∀ w : ℝ, 0 < w → volume (levelSet F a T w) ≤
      ENNReal.ofReal (A / w ^ 2 + B / w ^ 6)) :
    (∫ t in Icc a (a + T), ‖F t‖ ^ p) ≤
      v ^ (p - 2) * (∫ t in Icc a (a + T), ‖F t‖ ^ 2) +
        (J : ℝ) * (2 : ℝ) ^ p *
          (A * ((2 : ℝ) ^ J * v) ^ (p - 2) + B * v ^ (p - 6)) := by
  have hterm (j : ℕ) (hj : j ∈ Finset.range J) :
      ((2 : ℝ) ^ (j + 1) * v) ^ p * volume.real (levelSet F a T ((2 : ℝ) ^ j * v)) ≤
        (2 : ℝ) ^ p * (A * ((2 : ℝ) ^ J * v) ^ (p - 2) + B * v ^ (p - 6)) := by
    let w := (2 : ℝ) ^ j * v
    have hw : 0 < w := by dsimp [w]; positivity
    have hvw : v ≤ w := by
      dsimp [w]
      have hh := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := j)
      nlinarith
    have hwU : w ≤ (2 : ℝ) ^ J * v := by
      dsimp [w]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Finset.mem_range.mp hj).le) hv.le
    have hmeasure := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hlevel w hw)
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ A / w ^ 2 + B / w ^ 6)] at hmeasure
    change volume.real (levelSet F a T w) ≤ A / w ^ 2 + B / w ^ 6 at hmeasure
    have hheight : (2 : ℝ) ^ (j + 1) * v = 2 * w := by dsimp [w]; ring
    change ((2 : ℝ) ^ (j + 1) * v) ^ p * volume.real (levelSet F a T w) ≤ _
    rw [hheight]
    calc
      _ ≤ (2 * w) ^ p * (A / w ^ 2 + B / w ^ 6) :=
        mul_le_mul_of_nonneg_left hmeasure (Real.rpow_nonneg (by positivity) _)
      _ = (2 : ℝ) ^ p * (A * w ^ (p - 2) + B * w ^ (p - 6)) :=
        level_term_algebra w p A B hw
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (add_le_add
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hw.le hwU (by linarith)) hA)
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hv hvw (by linarith)) hB))
        (by positivity)
  apply (DyadicMoment.integral_bound F a T v p J hF hv hp hcap).trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ _j ∈ Finset.range J, (2 : ℝ) ^ p *
        (A * ((2 : ℝ) ^ J * v) ^ (p - 2) + B * v ^ (p - 6)) :=
      Finset.sum_le_sum hterm
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end LargeValueMoment

#print axioms LargeValueMoment.integral_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``LargeValueMoment.integral_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "LARGE VALUE MOMENT PASSED"
