import Item1LinearPhaseSum
import Mathlib.Algebra.Order.Round

/-! Linear phase estimates in terms of distance to the nearest integer.
The zero-distance branch keeps the full length instead of dividing by zero. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Item1LinearPhaseDistance
open Item1PhasePerturbation Item1LinearPhaseSum

def integerDistance (x : ℝ) : ℝ := |x-(round x:ℝ)|

def distanceBound (N : ℕ) (x : ℝ) : ℝ := by
  classical
  exact if integerDistance x = 0 then (N:ℝ)
    else min (N:ℝ) (1/(2*integerDistance x))

theorem integerDistance_nonneg (x : ℝ) : 0 ≤ integerDistance x := abs_nonneg _

theorem integerDistance_le_half (x : ℝ) : integerDistance x ≤ 1/2 := abs_sub_round x

/-- The chord of the unit circle is at least four times the distance to an integer. -/
theorem four_mul_distance_le_chord (x : ℝ) :
    4*integerDistance x ≤ ‖unitPhase (2*Real.pi*x)-1‖ := by
  have hperiod : |Real.sin (Real.pi*(x-(round x:ℝ)))| = |Real.sin (Real.pi*x)| := by
    rw [show Real.pi*(x-(round x:ℝ)) = Real.pi*x-(round x:ℝ)*Real.pi by ring,
      Real.sin_sub_int_mul_pi]
    simp only [abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  have habs : |Real.pi*(x-(round x:ℝ))| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [abs_sub_round x, Real.pi_pos]
  have hsine := Real.le_sin_mul
    (show 0 ≤ 2*integerDistance x by exact mul_nonneg (by norm_num) (integerDistance_nonneg x))
    (show 2*integerDistance x ≤ 1 by linarith [integerDistance_le_half x])
  have hsine' : 2*integerDistance x ≤ |Real.sin (Real.pi*x)| := by
    rw [← hperiod, Real.abs_sin_eq_sin_abs_of_abs_le_pi habs,
      abs_mul, abs_of_pos Real.pi_pos]
    convert hsine using 1 <;> congr 1 <;> unfold integerDistance <;> ring
  have hchord : ‖unitPhase (2*Real.pi*x)-1‖ = 2*|Real.sin (Real.pi*x)| := by
    unfold unitPhase
    rw [mul_comm (((2*Real.pi*x:ℝ):ℂ)) Complex.I,
      Complex.norm_exp_I_mul_ofReal_sub_one,
      show (2*Real.pi*x)/2 = Real.pi*x by ring,
      Real.norm_eq_abs, abs_mul]
    norm_num
  rw [hchord]
  linarith

theorem distanceBound_nonneg (N : ℕ) (x : ℝ) : 0 ≤ distanceBound N x := by
  classical
  unfold distanceBound
  split_ifs
  · positivity
  · exact le_min (by positivity) (div_nonneg (by norm_num)
      (mul_nonneg (by norm_num) (integerDistance_nonneg x)))

/-- The usual min(length, reciprocal-distance) estimate, with resonance handled. -/
theorem norm_phaseSum_le_distance_bound (N : ℕ) (x : ℝ) :
    ‖phaseSum N (2*Real.pi*x)‖ ≤ distanceBound N x := by
  classical
  have hlen : ‖phaseSum N (2*Real.pi*x)‖ ≤ (N:ℝ) := by
    rw [phaseSum_eq_geom_sum]
    exact norm_geom_sum_le_length _ (unitPhase_norm _) N
  unfold distanceBound
  split_ifs with hzero
  · exact hlen
  · refine le_min hlen ?_
    have hd : 0 < integerDistance x := lt_of_le_of_ne (integerDistance_nonneg x) (Ne.symm hzero)
    have hm := norm_geom_sum_mul_chord_le_two (unitPhase (2*Real.pi*x)) (unitPhase_norm _) N
    rw [← phaseSum_eq_geom_sum] at hm
    have hc := mul_le_mul_of_nonneg_left (four_mul_distance_le_chord x)
      (norm_nonneg (phaseSum N (2*Real.pi*x)))
    apply (le_div_iff₀ (show 0 < 2*integerDistance x by positivity)).mpr
    nlinarith

theorem norm_sum_Icc_zero_le_distance_bound (N : ℕ) (x : ℝ) :
    ‖∑ k ∈ Finset.Icc (0:ℤ) (N:ℤ), unitPhase ((2*Real.pi*x)*(k:ℝ))‖ ≤
      distanceBound (N+1) x := by
  rw [Int.Icc_eq_finset_map, Finset.sum_map]
  simpa [phaseSum, mul_comm] using norm_phaseSum_le_distance_bound (N+1) x

end Item1LinearPhaseDistance

run_cmd do
  for target in [``Item1LinearPhaseDistance.integerDistance_nonneg,
      ``Item1LinearPhaseDistance.integerDistance_le_half,
      ``Item1LinearPhaseDistance.four_mul_distance_le_chord,
      ``Item1LinearPhaseDistance.distanceBound_nonneg,
      ``Item1LinearPhaseDistance.norm_phaseSum_le_distance_bound,
      ``Item1LinearPhaseDistance.norm_sum_Icc_zero_le_distance_bound] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "LINEAR PHASE DISTANCE: 6 standard-axiom theorem guards passed."
