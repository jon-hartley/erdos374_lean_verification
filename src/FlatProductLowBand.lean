import FlatLowMoment
import SmoothedDirichletKernel

/-!
Low-frequency product energy from one flat factor. The remaining two
factors enter through their actual absolute coefficient masses. No
smallness of those masses is presumed or asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set

namespace FlatProductLowBand
open Erdos374.HarmanGram152 SmoothedDirichletKernel

theorem mean_square_bound (K lo hi : ℕ) (sm sn : Finset ℕ)
    (am an : ℕ → ℂ) (H U σ : ℝ) (hK : 1 ≤ K)
    (hlo : K ≤ lo) (hhi : hi ≤ 2 * K) (hH : 0 < H)
    (hU : U ≤ (K : ℝ)) (hσ : 1 ≤ σ)
    (hsm : ∀ n ∈ sm, 0 < n) (hsn : ∀ n ∈ sn, 0 < n) :
    (∫ t in Icc H U,
      ‖verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t *
        verticalDirichlet152 sm am σ t * verticalDirichlet152 sn an σ t‖ ^ 2) ≤
          ((16 * Real.pi) * coefficientMass sm am σ * coefficientMass sn an σ) ^ 2 / H := by
  let A := ((16 * Real.pi) * coefficientMass sm am σ * coefficientMass sn an σ) ^ 2
  have hm := mass_nonnegative sm am σ
  have hn := mass_nonnegative sn an σ
  have htail : IntegrableOn (fun t : ℝ => A * t ^ (-2 : ℝ)) (Ioi H) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hH).const_mul A
  have hsub : Ioc H U ⊆ Ioi H := fun _ ht => ht.1
  rw [integral_Icc_eq_integral_Ioc]
  calc
    _ ≤ ∫ t in Ioc H U, A * t ^ (-2 : ℝ) := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) (htail.mono_set hsub)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have htpos : 0 < t := hH.trans ht.1
      have hf := FlatLowFrequency.interval_bound K lo hi t σ hK hlo hhi
        (by rwa [abs_of_pos htpos]) (by simpa only [abs_of_pos htpos] using ht.2.trans hU) hσ
      rw [abs_of_pos htpos] at hf
      have hproduct :
          ‖verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t *
            verticalDirichlet152 sm am σ t * verticalDirichlet152 sn an σ t‖ ≤
              (16 * Real.pi) / t * coefficientMass sm am σ * coefficientMass sn an σ := by
        rw [norm_mul, norm_mul]
        apply mul_le_mul _ (polynomial_norm_le sn an σ t hsn) (norm_nonneg _) (by positivity)
        exact mul_le_mul hf (polynomial_norm_le sm am σ t hsm) (norm_nonneg _) (by positivity)
      calc
        _ ≤ ((16 * Real.pi) / t * coefficientMass sm am σ * coefficientMass sn an σ) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hproduct 2
        _ = _ := by
          dsimp [A]
          rw [Real.rpow_neg htpos.le]
          norm_num
          ring
    _ ≤ ∫ t in Ioi H, A * t ^ (-2 : ℝ) :=
      setIntegral_mono_set htail (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg (by dsimp [A]; positivity)
          (Real.rpow_nonneg (hH.trans ht).le _))
        (Filter.Eventually.of_forall hsub)
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hH]
      norm_num [A, Real.rpow_neg_one]
      ring

end FlatProductLowBand

#print axioms FlatProductLowBand.mean_square_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``FlatProductLowBand.mean_square_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "FLAT PRODUCT LOW BAND PASSED"
