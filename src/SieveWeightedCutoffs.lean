import SieveWeightedScalarBudget
import PrimeEulerDimensionOne
import SieveFiniteBase

/-! Pointwise geometry of the source's two varying upper cutoffs.
The common comparison exponent is beta, since the fourth cutoff can exceed
the first cutoff X^alpha. No weighted prime-sum estimate is assumed here. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real
namespace SieveWeightedCutoffs
open SieveWeightedScalarBudget SieveStoppingExpansion

def level (X s : ℝ) : ℝ := X^(1-3*s)
def cutoffThree (X s p : ℝ) : ℝ := (level X s/p)^(1/3:ℝ)
def cutoffFour (X s p : ℝ) : ℝ := (X^(upperExponent s)/p)^(1/2:ℝ)

theorem exponent_geometry (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1/1000) :
    (8/35:ℝ) ≤ alpha s ∧ alpha s ≤ beta s ∧
      (1/7:ℝ) ≤ beta s ∧ (9/35:ℝ) ≤ upperExponent s ∧
      2*beta s = upperExponent s-alpha s := by
  unfold alpha beta upperExponent
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  ring

theorem source_parameters (X s : ℝ) (hX : 1 < X)
    (hs : 0 ≤ s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ log X) :
    0 < alpha s ∧ alpha s ≤ (9/35:ℝ) ∧ 0 ≤ beta s ∧
      (9/35:ℝ) ≤ topExponent (1/log X) ∧
      topExponent (1/log X) < 1-3*s ∧ (9/35:ℝ) < upperExponent s := by
  have hL := log_pos hX
  have ht := log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
  have ht0 : 0 ≤ log 2 := (log_pos (by norm_num : (1:ℝ) < 2)).le
  have he : log 2/log X ≤ 1/1000 :=
    (div_le_iff₀ hL).mpr (by linarith)
  have he0 : 0 ≤ log 2/log X := div_nonneg ht0 hL.le
  have hid : topExponent (1/log X) = 1/2+(log 2/log X)/2 := by
    unfold topExponent
    ring
  rw [hid]
  unfold alpha beta upperExponent
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem sqrt_eq_top_power (X : ℝ) (hX : 1 < X) :
    sqrt (2*X) = X^(topExponent (1/log X)) := by
  have hX0 : 0 < X := by linarith
  apply log_injOn_pos (sqrt_pos.mpr (by positivity)) (rpow_pos_of_pos hX0 _)
  rw [log_sqrt (by positivity), log_mul (by norm_num) hX0.ne', log_rpow hX0]
  unfold topExponent
  field_simp [(log_pos hX).ne']
  ring

theorem three_pos (X s p : ℝ) (hX : 0 < X) (hp : 0 < p) :
    0 < cutoffThree X s p := by
  unfold cutoffThree level
  positivity

theorem four_pos (X s p : ℝ) (hX : 0 < X) (hp : 0 < p) :
    0 < cutoffFour X s p := by
  unfold cutoffFour
  positivity

theorem log_three (X s p : ℝ) (hX : 0 < X) (hp : 0 < p) :
    log (cutoffThree X s p) = ((1-3*s)*log X-log p)/3 := by
  unfold cutoffThree level
  rw [log_rpow (div_pos (rpow_pos_of_pos hX _) hp),
    log_div (rpow_pos_of_pos hX _).ne' hp.ne', log_rpow hX]
  ring

theorem log_four (X s p : ℝ) (hX : 0 < X) (hp : 0 < p) :
    log (cutoffFour X s p) = (upperExponent s*log X-log p)/2 := by
  unfold cutoffFour
  rw [log_rpow (div_pos (rpow_pos_of_pos hX _) hp),
    log_div (rpow_pos_of_pos hX _).ne' hp.ne', log_rpow hX]
  ring

theorem three_cube (X s p : ℝ) (hX : 0 < X) (hp : 0 < p) :
    cutoffThree X s p^3 = level X s/p := by
  unfold cutoffThree level
  rw [← rpow_natCast, ← rpow_mul (div_pos (rpow_pos_of_pos hX _) hp).le]
  norm_num

theorem two_le_floor_cutoff (X : ℝ) (hX : 1 < X) (hlog : 1000 ≤ log X) :
    2 ≤ X^(1/7:ℝ) := by
  apply (log_le_log_iff (by norm_num) (rpow_pos_of_pos (by linarith) _)).mp
  rw [log_rpow (by linarith)]
  have hh := log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
  linarith

theorem three_log_range (X s p : ℝ) (hX : 1 < X)
    (hs : 0 ≤ s) (hs1 : s ≤ 1/1000)
    (hlog : 1000 ≤ log X) (hplo : X^(9/35:ℝ) ≤ p)
    (hphi : p ≤ sqrt (2*X)) :
    log X/7 ≤ log (cutoffThree X s p) ∧
      log (cutoffThree X s p) ≤ beta s*log X := by
  have hX0 : 0 < X := by linarith
  have hp : 0 < p := (rpow_pos_of_pos hX0 _).trans_le hplo
  have hlo := log_le_log (rpow_pos_of_pos hX0 (9/35:ℝ)) hplo
  rw [log_rpow hX0] at hlo
  have hhi := log_le_log hp hphi
  rw [log_sqrt (by positivity), log_mul (by norm_num) hX0.ne'] at hhi
  have ht := log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
  have hsl := mul_le_mul_of_nonneg_right hs1 (log_pos hX).le
  have hsn := mul_nonneg hs (log_pos hX).le
  rw [log_three X s p hX0 hp]
  unfold beta
  constructor <;> nlinarith

theorem three_geometry (X s p : ℝ) (hX : 1 < X)
    (hs : 0 ≤ s) (hs1 : s ≤ 1/1000)
    (hlog : 1000 ≤ log X) (hplo : X^(9/35:ℝ) ≤ p)
    (hphi : p ≤ sqrt (2*X)) :
    X^(1/7:ℝ) ≤ cutoffThree X s p ∧
      cutoffThree X s p ≤ X^(beta s) ∧ cutoffThree X s p^3 ≤ level X s/p := by
  have hX0 : 0 < X := by linarith
  have hp : 0 < p := (rpow_pos_of_pos hX0 _).trans_le hplo
  obtain ⟨hlo, hhi⟩ := three_log_range X s p hX hs hs1 hlog hplo hphi
  refine ⟨?_, ?_, (three_cube X s p hX0 hp).le⟩
  · apply (log_le_log_iff (rpow_pos_of_pos hX0 _) (three_pos X s p hX0 hp)).mp
    simpa only [log_rpow hX0, div_eq_mul_inv, one_mul, mul_comm] using hlo
  · apply (log_le_log_iff (three_pos X s p hX0 hp) (rpow_pos_of_pos hX0 _)).mp
    simpa only [log_rpow hX0] using hhi

theorem four_log_range (X s p : ℝ) (hX : 1 < X)
    (hs : 0 ≤ s) (hs1 : s ≤ 1/1000)
    (hplo : X^(alpha s) ≤ p) (hphi : p ≤ X^(9/35:ℝ)) :
    log X/7 ≤ log (cutoffFour X s p) ∧
      log (cutoffFour X s p) ≤ beta s*log X := by
  have hX0 : 0 < X := by linarith
  have hp : 0 < p := (rpow_pos_of_pos hX0 _).trans_le hplo
  have hlo := log_le_log (rpow_pos_of_pos hX0 (alpha s)) hplo
  rw [log_rpow hX0] at hlo
  have hhi := log_le_log hp hphi
  rw [log_rpow hX0] at hhi
  have hsl := mul_le_mul_of_nonneg_right hs1 (log_pos hX).le
  have hsn := mul_nonneg hs (log_pos hX).le
  rw [log_four X s p hX0 hp]
  unfold beta alpha upperExponent at *
  constructor <;> nlinarith

theorem four_level (X s p : ℝ) (hX : 1 < X)
    (hs : 0 ≤ s) (hs1 : s ≤ 1/1000) (hplo : X^(alpha s) ≤ p) :
    cutoffFour X s p^3 ≤ level X s/p := by
  have hX0 : 0 < X := by linarith
  have hp : 0 < p := (rpow_pos_of_pos hX0 _).trans_le hplo
  have hlo := log_le_log (rpow_pos_of_pos hX0 (alpha s)) hplo
  rw [log_rpow hX0] at hlo
  have hlow := mul_le_mul_of_nonneg_right (exponent_geometry s hs hs1).1 (log_pos hX).le
  apply (log_le_log_iff (pow_pos (four_pos X s p hX0 hp) _)
    (div_pos (rpow_pos_of_pos hX0 _) hp)).mp
  rw [log_pow, log_four X s p hX0 hp]
  rw [log_div (rpow_pos_of_pos hX0 _).ne' hp.ne', log_rpow hX0]
  norm_num
  unfold upperExponent at *
  nlinarith

theorem four_geometry (X s p : ℝ) (hX : 1 < X)
    (hs : 0 ≤ s) (hs1 : s ≤ 1/1000)
    (hplo : X^(alpha s) ≤ p) (hphi : p ≤ X^(9/35:ℝ)) :
    X^(1/7:ℝ) ≤ cutoffFour X s p ∧
      cutoffFour X s p ≤ X^(beta s) ∧ cutoffFour X s p^3 ≤ level X s/p := by
  have hX0 : 0 < X := by linarith
  have hp : 0 < p := (rpow_pos_of_pos hX0 _).trans_le hplo
  obtain ⟨hlo, hhi⟩ := four_log_range X s p hX hs hs1 hplo hphi
  refine ⟨?_, ?_, four_level X s p hX hs hs1 hplo⟩
  · apply (log_le_log_iff (rpow_pos_of_pos hX0 _) (four_pos X s p hX0 hp)).mp
    simpa only [log_rpow hX0, div_eq_mul_inv, one_mul, mul_comm] using hlo
  · apply (log_le_log_iff (four_pos X s p hX0 hp) (rpow_pos_of_pos hX0 _)).mp
    simpa only [log_rpow hX0] using hhi

theorem euler_comparison (X s w : ℝ) (hX : 1 < X)
    (hs : 0 ≤ s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ log X)
    (hwlo : X^(1/7:ℝ) ≤ w) (hwhi : w ≤ X^(beta s)) :
    primeEuler w / primeEuler (X^(alpha s)) ≤
      (beta s*log X/log w)*exp (84/log X) := by
  have hX0 : 0 < X := by linarith
  have hw2 := (two_le_floor_cutoff X hX hlog).trans hwlo
  have hw0 : 0 < w := by linarith
  have hwlog : 0 < log w := log_pos (by linarith)
  have hbeta := (exponent_geometry s hs hs1).2.1
  have heuler := SieveFiniteBase.euler_antitone (X^(alpha s)) (X^(beta s))
    (rpow_le_rpow_of_exponent_le hX.le hbeta)
  have hratio : primeEuler w/primeEuler (X^(alpha s)) ≤
      primeEuler w/primeEuler (X^(beta s)) :=
    div_le_div_of_nonneg_left (SieveEulerRatio.euler_pos w).le
      (SieveEulerRatio.euler_pos _) heuler
  have hbase := hratio.trans (PrimeEulerDimensionOne.ratio_bound_exp _ _ hw2 hwhi)
  rw [log_rpow hX0] at hbase
  have hlower := log_le_log (rpow_pos_of_pos hX0 (1/7:ℝ)) hwlo
  rw [log_rpow hX0] at hlower
  have hexponent : 12/log w ≤ 84/log X :=
    (div_le_div_iff₀ hwlog (log_pos hX)).mpr (by nlinarith)
  have hbnonneg : 0 ≤ beta s*log X/log w := by
    have hb := (exponent_geometry s hs hs1).2.2.1
    exact div_nonneg (mul_nonneg (by linarith) (log_pos hX).le) hwlog.le
  exact hbase.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr hexponent) hbnonneg)

theorem euler_three (X s p : ℝ) (hX : 1 < X)
    (hs : 0 ≤ s) (hs1 : s ≤ 1/1000)
    (hlog : 1000 ≤ log X) (hplo : X^(9/35:ℝ) ≤ p)
    (hphi : p ≤ sqrt (2*X)) :
    primeEuler (cutoffThree X s p)/primeEuler (X^(alpha s)) ≤
      (3*beta s/(1-3*s-log p/log X))*exp (84/log X) := by
  have hX0 : 0 < X := by linarith
  have hp : 0 < p := (rpow_pos_of_pos hX0 _).trans_le hplo
  obtain ⟨hlo, hhi, _⟩ := three_geometry X s p hX hs hs1 hlog hplo hphi
  have hh := euler_comparison X s (cutoffThree X s p) hX hs hs1 hlog hlo hhi
  have hl := (three_log_range X s p hX hs hs1 hlog hplo hphi).1
  rw [log_three X s p hX0 hp] at hl hh
  have hden : 0 < (1-3*s)*log X-log p := by linarith [log_pos hX]
  have hden' : 0 < 1-3*s-log p/log X :=
    sub_pos.mpr ((div_lt_iff₀ (log_pos hX)).mpr (by linarith))
  convert hh using 1
  field_simp [(log_pos hX).ne', hden.ne', hden'.ne']

theorem euler_four (X s p : ℝ) (hX : 1 < X)
    (hs : 0 ≤ s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ log X)
    (hplo : X^(alpha s) ≤ p) (hphi : p ≤ X^(9/35:ℝ)) :
    primeEuler (cutoffFour X s p)/primeEuler (X^(alpha s)) ≤
      (2*beta s/(upperExponent s-log p/log X))*exp (84/log X) := by
  have hX0 : 0 < X := by linarith
  have hp : 0 < p := (rpow_pos_of_pos hX0 _).trans_le hplo
  obtain ⟨hlo, hhi, _⟩ := four_geometry X s p hX hs hs1 hplo hphi
  have hh := euler_comparison X s (cutoffFour X s p) hX hs hs1 hlog hlo hhi
  have hl := (four_log_range X s p hX hs hs1 hplo hphi).1
  rw [log_four X s p hX0 hp] at hl hh
  have hden : 0 < upperExponent s*log X-log p := by linarith [log_pos hX]
  have hden' : 0 < upperExponent s-log p/log X :=
    sub_pos.mpr ((div_lt_iff₀ (log_pos hX)).mpr (by linarith))
  convert hh using 1
  field_simp [(log_pos hX).ne', hden.ne', hden'.ne']

run_cmd do
  for decl in [``exponent_geometry, ``source_parameters, ``sqrt_eq_top_power,
      ``three_pos, ``four_pos, ``log_three, ``log_four,
      ``three_cube, ``two_le_floor_cutoff, ``three_log_range, ``three_geometry,
      ``four_log_range, ``four_level, ``four_geometry, ``euler_comparison,
      ``euler_three, ``euler_four] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL VARYING UPPER CUTOFF GEOMETRY; ORDERED BETA EULER COMPARISON"
end SieveWeightedCutoffs
end
