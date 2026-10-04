import FlatLowFrequency
import PowerIntegralTail
import NormalizedMeanSquare

/-!
The low-frequency eighth moment has an integrable inverse-eighth-power
majorant. Its bound is uniform in the upper endpoint up to the length N.
This handles flat polynomials only, with sigma at least one.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Set

namespace FlatLowMoment
open Erdos374.HarmanGram152

theorem eighth_bound (N lo hi : ℕ) (H U σ : ℝ) (hN : 1 ≤ N)
    (hlo : N ≤ lo) (hhi : hi ≤ 2 * N) (hH : 0 < H)
    (hU : U ≤ (N : ℝ)) (hσ : 1 ≤ σ) :
    (∫ t in Icc H U,
      ‖verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t‖ ^ (8 : ℕ)) ≤
        (16 * Real.pi) ^ (8 : ℕ) * H ^ (-7 : ℝ) / 7 := by
  let A : ℝ := (16 * Real.pi) ^ (8 : ℕ)
  have htail : IntegrableOn (fun t : ℝ => A * t ^ (-8 : ℝ)) (Ioi H) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-8 : ℝ) < -1) hH).const_mul A
  have hsub : Ioc H U ⊆ Ioi H := fun _ ht => ht.1
  rw [integral_Icc_eq_integral_Ioc]
  calc
    _ ≤ ∫ t in Ioc H U, A * t ^ (-8 : ℝ) := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun _ => by positivity)) (htail.mono_set hsub)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have htpos : 0 < t := hH.trans ht.1
      have hh := FlatLowFrequency.interval_bound N lo hi t σ hN hlo hhi
        (by rwa [abs_of_pos htpos]) (by simpa only [abs_of_pos htpos] using ht.2.trans hU) hσ
      rw [abs_of_pos htpos] at hh
      calc
        _ ≤ ((16 * Real.pi) / t) ^ (8 : ℕ) := pow_le_pow_left₀ (norm_nonneg _) hh 8
        _ = _ := by
          dsimp [A]
          rw [Real.rpow_neg htpos.le, div_pow, div_eq_mul_inv]
          norm_num
    _ ≤ ∫ t in Ioi H, A * t ^ (-8 : ℝ) :=
      setIntegral_mono_set htail (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg (by dsimp [A]; positivity)
          (Real.rpow_nonneg (hH.trans ht).le _))
        (Filter.Eventually.of_forall hsub)
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-8 : ℝ) < -1) hH]
      norm_num [A]
      ring

end FlatLowMoment

#print axioms FlatLowMoment.eighth_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``FlatLowMoment.eighth_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "FLAT LOW MOMENT PASSED"
