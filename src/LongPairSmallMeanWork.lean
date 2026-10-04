import LongPairSmallProfileFirstMeanWork

/-! Exact short-pair assembly and its complete literal absolute mean. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LongPairSmallMeanWork
open LongPairProfilesWork ShortPairSplitWork LongPairSmallProfileFirstMeanWork
open LongerTupleActualProfiles LongerTupleHigherMeanWork LongerTupleSector
open LongerTupleProfile SieveWeightedCutoffs SieveBoxedFamily UpperAfter545Sectors
open UpperAfter545Remaining PositiveSharpPowerWindow PositiveSharpBoxedCount
open SieveCappedUpperMainTerms (cappedFourth)

def pairProfiles (s : ℝ) : Finset (List ℕ) := (profiles true s).filter (fun js => js.length=2)
def branchBand (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (second : Bool) (f : ℕ → ℝ) : ℝ :=
  selectedKernel X s P z true (fun t => t.length=2 ∧ chosen X second (0,0,t)) f

theorem branchBand_eq_profiles (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (hs : 0<s) (hg : BandGeometry X s P z) (f : ℕ → ℝ) :
    branchBand X s P z second f = ∑ js ∈ pairProfiles s, pairKernel X s P z second js f := by
  let J := pairProfiles s
  have htup (p : ℕ) (hp : p∈P) (d : ℕ) :
      (∑ t ∈ (family true (level X s/p) s (z p)).filter
          (fun t => t.length=2 ∧ chosen X second (p,d,t)),
        SieveSmallWeights.weight ((level X s/p)^s) ((level X s/p)^(s^2)) true d *
          highKernel X f (p*(d*t.prod))) =
      ∑ js ∈ J, ∑ t ∈ (family true (level X s/p) s (z p)).filter
          (fun t => indices (level X s/p) s t=js ∧ chosen X second (p,d,t)),
        SieveSmallWeights.weight ((level X s/p)^s) ((level X s/p)^(s^2)) true d *
          highKernel X f (p*(d*t.prod)) := by
    have maps : ∀ t∈(family true (level X s/p) s (z p)).filter
        (fun t => t.length=2 ∧ chosen X second (p,d,t)), indices (level X s/p) s t ∈ J := by
      intro t ht
      obtain ⟨ht,hlen,_⟩ := Finset.mem_filter.mp ht
      apply Finset.mem_filter.mpr
      exact ⟨((family_fixed_iff true _ s _ (hg p hp).2.2.1 hs (hg p hp).2.2.2
        t (indices (level X s/p) s t)).mp ⟨ht,rfl⟩).1,
        by simpa only [indices,List.length_map] using hlen⟩
    rw [←Finset.sum_fiberwise_of_maps_to maps]
    apply Finset.sum_congr rfl
    intro js hjs
    apply Finset.sum_congr
    · ext t
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨ht,_,hc⟩,he⟩
        exact ⟨ht,he,hc⟩
      · rintro ⟨ht,he,hc⟩
        have hlen : t.length=js.length := by
          simpa only [indices,List.length_map] using congrArg List.length he
        exact ⟨⟨ht,hlen.trans (Finset.mem_filter.mp hjs).2,hc⟩,he⟩
    · intro t _; rfl
  calc
    _ = ∑ p∈P, ∑ d∈SieveUpperBoxWindow.smallCarrier (level X s/p) s,
        ∑ t∈(family true (level X s/p) s (z p)).filter
          (fun t => t.length=2 ∧ chosen X second (p,d,t)),
          SieveSmallWeights.weight ((level X s/p)^s) ((level X s/p)^(s^2)) true d *
            highKernel X f (p*(d*t.prod)) := by
      unfold branchBand selectedKernel family chosen ShortPairSplitWork.prime ShortPairSplitWork.drop
      congr!
    _ = ∑ p∈P, ∑ d∈SieveUpperBoxWindow.smallCarrier (level X s/p) s,
        ∑ js∈J, ∑ t∈(family true (level X s/p) s (z p)).filter
          (fun t => indices (level X s/p) s t=js ∧ chosen X second (p,d,t)),
          SieveSmallWeights.weight ((level X s/p)^s) ((level X s/p)^(s^2)) true d *
            highKernel X f (p*(d*t.prod)) := by
      apply Finset.sum_congr rfl; intro p hp
      apply Finset.sum_congr rfl; intro d _
      exact htup p hp d
    _ = _ := by
      simp_rw [Finset.sum_comm (s:=SieveUpperBoxWindow.smallCarrier (level X s/_) s) (t:=J)]
      rw [Finset.sum_comm]
      unfold pairKernel
      congr!

open LongPairSmallProfileMeanWork


theorem longPairBand_eq_profiles (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (hs : 0<s) (hg : BandGeometry X s P z) (f : ℕ → ℝ) :
    longPairBand X s P z f = ∑ js∈pairProfiles s,pairKernel X s P z true js f := by
  have he : (fun t : List ℕ => t.length=2 ∧ allLong X t) =
      (fun t : List ℕ => t.length=2 ∧ chosen X true (0,0,t)) := by
    funext t
    apply propext
    by_cases hlen : t.length=2
    · simp only [hlen,true_and]
      exact (chosen_iff_allLong X true (0,0,t) hlen).symm
    · simp only [hlen,false_and]
  unfold longPairBand
  rw [he]
  exact branchBand_eq_profiles X s P z true hs hg f

theorem pair_moving_integrable (X s Y : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) :
    IntegrableOn (fun x => pairKernel X s P z second js
      (floorKernel (x-x*(Y/X)) x)) (Icc X (2*X)) := by
  simp_rw [LongPairSmallProfileFirstMeanWork.profile_eq_remainder]
  simpa only [mul_div_assoc] using TailRemainderBand.moving_remainder_integrable
    (LongPairSmallProfileFirstMeanWork.divisorSupport X s P z second js)
    (LongPairSmallProfileFirstMeanWork.divisorCoefficient X s P z second js) X Y

/-- Entire literal small-band long-pair sector, every fixed logarithmic power.
No sector mean or separability hypothesis remains. -/
theorem eventually_small_longPair_absolute_log (s : ℝ) (A : ℕ)
    (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ 1000≤Real.log X ∧
      let Y := halfWidth X (101/1000)
      (1/X)*(∫ x in Icc X (2*X), |longPairBand X s (smallPrimes X s)
        (cappedFourth X s) (floorKernel (x-x*(Y/X)) x)|) ≤
        ((pairProfiles s).card:ℝ)*Y/(Real.log X)^A := by
  filter_upwards [eventually_pair_absolute_log s A hs hs1] with X hm
  refine ⟨hm.1,hm.2.1,?_⟩
  dsimp only
  let Y := halfWidth X (101/1000)
  have hg := small_band_geometry X s hm.1 hs hs1 hm.2.1
  simp_rw [longPairBand_eq_profiles X s _ _ hs hg]
  apply (absolute_sum_mean_le (pairProfiles s)
    (fun js x => pairKernel X s (smallPrimes X s) (cappedFourth X s) true js
      (floorKernel (x-x*(Y/X)) x)) X (by linarith [hm.1])
    (fun js _ => pair_moving_integrable X s Y _ _ true js)).trans
  calc
    _ ≤ ∑ js∈pairProfiles s,Y/(Real.log X)^A := Finset.sum_le_sum
      (fun js hjs => hm.2.2 true js (Finset.mem_filter.mp hjs).2)
    _ = _ := by simp; ring

theorem eventually_small_longPair_absolute_log_unit (s : ℝ) (A : ℕ)
    (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ 1000≤Real.log X ∧
      let Y := halfWidth X (101/1000)
      (1/X)*(∫ x in Icc X (2*X), |longPairBand X s (smallPrimes X s)
        (cappedFourth X s) (floorKernel (x-x*(Y/X)) x)|) ≤ Y/(Real.log X)^A := by
  filter_upwards [eventually_small_longPair_absolute_log s (A+1) hs hs1,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop ((pairProfiles s).card:ℝ)),
    halfWidth_eventually (101/1000) (by norm_num)] with X hm hcost hY
  refine ⟨hm.1,hm.2.1,hm.2.2.trans ?_⟩
  have hl : 0<Real.log X := Real.log_pos hm.1
  apply (div_le_div_iff₀ (pow_pos hl (A+1)) (pow_pos hl A)).mpr
  rw [pow_succ]
  have hh := mul_le_mul_of_nonneg_left hcost
    (mul_nonneg hY.1.le (pow_nonneg hl.le A))
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hh

#print axioms eventually_small_longPair_absolute_log_unit
run_cmd do
  for decl in [``branchBand_eq_profiles, ``longPairBand_eq_profiles,
      ``pair_moving_integrable, ``eventually_small_longPair_absolute_log,
      ``eventually_small_longPair_absolute_log_unit] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end LongPairSmallMeanWork

