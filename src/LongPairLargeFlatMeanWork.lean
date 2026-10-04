import LongPairLargeFlatProfileFirstMeanWork
import LongPairSmallMeanWork

/-! Complete large-band long-pair mean below the flat cap, and exact
separation of the still-unestimated complementary high-product strip. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LongPairLargeFlatMeanWork
open LongPairProfilesWork LongPairLargeFlatProfileMeanWork
open LongPairLargeFlatProfileFirstMeanWork LongerTupleActualProfiles
open LongerTupleHigherMeanWork LongerTupleSector LongPairSmallMeanWork
open SieveWeightedCutoffs UpperAfter545Remaining UpperAfter545Sectors
open PositiveSharpPowerWindow PositiveSharpBoxedCount

def flatBand (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (U : ℝ) (f : ℕ → ℝ) : ℝ :=
  longPairBand X s P z (fun m => if (m:ℝ)≤U then f m else 0)

def largeFlatRemainder (X s L R : ℝ) : ℝ :=
  flatBand X s (largePrimes X) (cutoffThree X s) (X^(26/35:ℝ)) (floorKernel L R)

def largeHighRemainder (X s L R : ℝ) : ℝ :=
  longPairBand X s (largePrimes X) (cutoffThree X s)
    (fun m => if X^(26/35:ℝ)<(m:ℝ) then floorKernel L R m else 0)

theorem longPairBand_add (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (f g : ℕ → ℝ) :
    longPairBand X s P z (fun m => f m+g m) =
      longPairBand X s P z f+longPairBand X s P z g := by
  have hk (m : ℕ) : highKernel X (fun m => f m+g m) m =
      highKernel X f m+highKernel X g m := by
    unfold highKernel
    split_ifs <;> simp
  unfold longPairBand selectedKernel
  simp_rw [hk,mul_add,Finset.sum_add_distrib]

theorem large_partition (X s L R : ℝ) :
    longPairBand X s (largePrimes X) (cutoffThree X s) (floorKernel L R) =
      largeFlatRemainder X s L R+largeHighRemainder X s L R := by
  unfold largeFlatRemainder flatBand largeHighRemainder
  rw [←longPairBand_add]
  congr 1
  funext m
  by_cases hc : (m:ℝ)≤X^(26/35:ℝ)
  · simp only [hc,not_lt_of_ge hc,ite_true,ite_false,add_zero]
  · simp only [hc,lt_of_not_ge hc,ite_false,ite_true,zero_add]

theorem flatBand_eq_profiles (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (hs : 0<s) (hg : BandGeometry X s P z) (U : ℝ) (f : ℕ → ℝ) :
    flatBand X s P z U f = ∑ js∈pairProfiles s,cappedKernel X s P z true js U f := by
  exact longPairBand_eq_profiles X s P z hs hg _

theorem capped_moving_integrable (X s Y U : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) :
    IntegrableOn (fun x => cappedKernel X s P z second js U
      (floorKernel (x-x*(Y/X)) x)) (Icc X (2*X)) := by
  simp_rw [LongPairLargeFlatProfileFirstMeanWork.profile_eq_remainder]
  simpa only [mul_div_assoc] using TailRemainderBand.moving_remainder_integrable
    (LongPairLargeFlatProfileFirstMeanWork.divisorSupport X s P z second js)
    (LongPairLargeFlatProfileFirstMeanWork.divisorCoefficient X s P z second js U) X Y

theorem eventually_largeFlat_absolute_log (s : ℝ) (A : ℕ)
    (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ 1000≤Real.log X ∧
      let Y := halfWidth X (101/1000)
      (1/X)*(∫ x in Icc X (2*X), |largeFlatRemainder X s (x-x*(Y/X)) x|) ≤
        ((pairProfiles s).card:ℝ)*Y/(Real.log X)^A := by
  filter_upwards [LongPairLargeFlatProfileFirstMeanWork.eventually_pair_absolute_log s A hs hs1]
    with X hm
  refine ⟨hm.1,hm.2.1,?_⟩
  dsimp only
  let Y := halfWidth X (101/1000)
  have hg := large_band_geometry X s hm.1 hs hs1 hm.2.1
  unfold largeFlatRemainder
  simp_rw [flatBand_eq_profiles X s _ _ hs hg]
  apply (absolute_sum_mean_le (pairProfiles s)
    (fun js x => cappedKernel X s (largePrimes X) (cutoffThree X s) true js (X^(26/35:ℝ))
      (floorKernel (x-x*(Y/X)) x)) X (by linarith [hm.1])
    (fun js _ => capped_moving_integrable X s Y _ _ _ true js)).trans
  calc
    _ ≤ ∑ js∈pairProfiles s,Y/(Real.log X)^A := Finset.sum_le_sum
      (fun js hjs => hm.2.2 true js (Finset.mem_filter.mp hjs).2)
    _ = _ := by simp; ring

/-- Every fixed inverse-log absolute mean for the exact covered part. -/
theorem eventually_largeFlat_absolute_log_unit (s : ℝ) (A : ℕ)
    (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ 1000≤Real.log X ∧
      let Y := halfWidth X (101/1000)
      (1/X)*(∫ x in Icc X (2*X), |largeFlatRemainder X s (x-x*(Y/X)) x|) ≤
        Y/(Real.log X)^A := by
  filter_upwards [eventually_largeFlat_absolute_log s (A+1) hs hs1,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop ((pairProfiles s).card:ℝ)),
    halfWidth_eventually (101/1000) (by norm_num)] with X hm hcost hY
  refine ⟨hm.1,hm.2.1,hm.2.2.trans ?_⟩
  have hl : 0<Real.log X := Real.log_pos hm.1
  apply (div_le_div_iff₀ (pow_pos hl (A+1)) (pow_pos hl A)).mpr
  rw [pow_succ]
  have hh := mul_le_mul_of_nonneg_left hcost
    (mul_nonneg hY.1.le (pow_nonneg hl.le A))
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hh

#print axioms large_partition
#print axioms eventually_largeFlat_absolute_log_unit
run_cmd do
  for decl in [``longPairBand_add, ``large_partition, ``flatBand_eq_profiles,
      ``capped_moving_integrable, ``eventually_largeFlat_absolute_log,
      ``eventually_largeFlat_absolute_log_unit] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end LongPairLargeFlatMeanWork
