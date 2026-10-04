import LongerTupleSectorWork
import LongerTupleProfileFirstMeanWork

/-! Exact finite profile assembly for the literal higher upper sector. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LongerTupleHigherMeanWork
open LongerTupleSector LongerTupleActualProfiles LongerTupleProfile
open LongerTupleProfileFirstMeanWork UpperAfter545Remaining
open SieveWeightedCutoffs SieveGeometricGrid UpperAfter545Sectors
open SieveBoxedFamily
open PositiveSharpBoxedCount PositiveSharpPowerWindow
open SieveCappedUpperMainTerms (cappedFourth)

def selectedProfiles (s : ℝ) (outer : Bool) (n : ℕ) : Finset (List ℕ) :=
  (profiles outer s).filter (fun js => n ≤ js.length)

theorem selectedKernel_eq_profiles (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (outer : Bool) (n : ℕ) (hs : 0 < s) (hg : BandGeometry X s P z) (f : ℕ → ℝ) :
    selectedKernel X s P z outer (fun t => n ≤ t.length) f =
      ∑ js ∈ selectedProfiles s outer n, profileKernel X s P z outer js f := by
  let J := selectedProfiles s outer n
  have htup (p : ℕ) (hp : p ∈ P) (d : ℕ) :
      (∑ t ∈ (family outer (level X s/p) s (z p)).filter (fun t => n ≤ t.length),
        SieveSmallWeights.weight ((level X s/p)^s) ((level X s/p)^(s^2)) outer d *
          highKernel X f (p*(d*t.prod))) =
      ∑ js ∈ J, ∑ t ∈ (family outer (level X s/p) s (z p)).filter
          (fun t => indices (level X s/p) s t = js),
        SieveSmallWeights.weight ((level X s/p)^s) ((level X s/p)^(s^2)) outer d *
          highKernel X f (p*(d*t.prod)) := by
    have maps : ∀ t ∈ (family outer (level X s/p) s (z p)).filter
        (fun t => n ≤ t.length), indices (level X s/p) s t ∈ J := by
      intro t ht
      obtain ⟨ht,hlen⟩ := Finset.mem_filter.mp ht
      apply Finset.mem_filter.mpr
      refine ⟨?_,by simpa only [indices, List.length_map] using hlen⟩
      exact ((family_fixed_iff outer _ s _ (hg p hp).2.2.1 hs (hg p hp).2.2.2
        t (indices (level X s/p) s t)).mp ⟨ht,rfl⟩).1
    rw [←Finset.sum_fiberwise_of_maps_to maps]
    apply Finset.sum_congr rfl
    intro js hjs
    apply Finset.sum_congr
    · ext t
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨ht,_⟩,he⟩
        exact ⟨ht,he⟩
      · rintro ⟨ht,he⟩
        have hlen : t.length = js.length := by
          simpa only [indices,List.length_map] using congrArg List.length he
        exact ⟨⟨ht,hlen ▸ (Finset.mem_filter.mp hjs).2⟩,he⟩
    · intro t _
      rfl
  calc
    _ = ∑ p ∈ P, ∑ d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s,
        ∑ t ∈ (family outer (level X s/p) s (z p)).filter (fun t => n ≤ t.length),
          SieveSmallWeights.weight ((level X s/p)^s) ((level X s/p)^(s^2)) outer d *
            highKernel X f (p*(d*t.prod)) := by
      unfold selectedKernel family
      congr!
    _ = ∑ p ∈ P, ∑ d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s,
        ∑ js ∈ J, ∑ t ∈ (family outer (level X s/p) s (z p)).filter
          (fun t => indices (level X s/p) s t = js),
          SieveSmallWeights.weight ((level X s/p)^s) ((level X s/p)^(s^2)) outer d *
            highKernel X f (p*(d*t.prod)) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro d _
      exact htup p hp d
    _ = _ := by
      simp_rw [Finset.sum_comm (s := SieveUpperBoxWindow.smallCarrier (level X s/_) s) (t := J)]
      rw [Finset.sum_comm]
      unfold profileKernel
      congr!

theorem higherBand_eq_profiles (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (hs : 0 < s) (hg : BandGeometry X s P z) (f : ℕ → ℝ) :
    higherBand X s P z f =
      (∑ js ∈ selectedProfiles s true 4, profileKernel X s P z true js f) -
      ∑ js ∈ selectedProfiles s false 3, profileKernel X s P z false js f := by
  unfold higherBand
  rw [selectedKernel_eq_profiles X s P z true 4 hs hg,
    selectedKernel_eq_profiles X s P z false 3 hs hg]

theorem profile_moving_integrable (X s Y : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (outer : Bool) (js : List ℕ) :
    IntegrableOn (fun x => profileKernel X s P z outer js
      (floorKernel (x-x*(Y/X)) x)) (Icc X (2*X)) := by
  simp_rw [profile_eq_remainder]
  simpa only [mul_div_assoc] using TailRemainderBand.moving_remainder_integrable
    (divisorSupport X s P z outer js) (divisorCoefficient X s P z outer js) X Y

theorem absolute_sum_mean_le {α : Type*} (J : Finset α) (f : α → ℝ → ℝ)
    (X : ℝ) (hX : 0 < X) (hf : ∀ i ∈ J, IntegrableOn (f i) (Icc X (2*X))) :
    (1/X)*(∫ x in Icc X (2*X), |∑ i ∈ J, f i x|) ≤
      ∑ i ∈ J, (1/X)*(∫ x in Icc X (2*X), |f i x|) := by
  have hs : IntegrableOn (fun x => ∑ i ∈ J, f i x) (Icc X (2*X)) :=
    integrable_finsetSum J hf
  have ha : IntegrableOn (fun x => ∑ i ∈ J, |f i x|) (Icc X (2*X)) :=
    integrable_finsetSum J (fun i hi => (hf i hi).abs)
  have hh := setIntegral_mono_on hs.abs ha measurableSet_Icc
    (fun x _ => Finset.abs_sum_le_sum_abs (fun i => f i x) J)
  rw [integral_finsetSum J (fun i hi => (hf i hi).abs)] at hh
  simpa only [Finset.mul_sum] using
    mul_le_mul_of_nonneg_left hh (one_div_nonneg.mpr hX.le)

theorem absolute_sub_mean_le (f g : ℝ → ℝ) (X : ℝ) (hX : 0 < X)
    (hf : IntegrableOn f (Icc X (2*X))) (hg : IntegrableOn g (Icc X (2*X))) :
    (1/X)*(∫ x in Icc X (2*X), |f x-g x|) ≤
      (1/X)*(∫ x in Icc X (2*X), |f x|) +
      (1/X)*(∫ x in Icc X (2*X), |g x|) := by
  have hh := setIntegral_mono_on (hf.sub hg).abs (hf.abs.add hg.abs)
    measurableSet_Icc (fun x _ => abs_sub (f x) (g x))
  simp only [Pi.add_apply, Pi.sub_apply] at hh
  rw [integral_add hf.abs hg.abs] at hh
  simpa only [mul_add] using mul_le_mul_of_nonneg_left hh (one_div_nonneg.mpr hX.le)

theorem absolute_add_mean_le (f g : ℝ → ℝ) (X : ℝ) (hX : 0 < X)
    (hf : IntegrableOn f (Icc X (2*X))) (hg : IntegrableOn g (Icc X (2*X))) :
    (1/X)*(∫ x in Icc X (2*X), |f x+g x|) ≤
      (1/X)*(∫ x in Icc X (2*X), |f x|) +
      (1/X)*(∫ x in Icc X (2*X), |g x|) := by
  have hh := setIntegral_mono_on (hf.add hg).abs (hf.abs.add hg.abs)
    measurableSet_Icc (fun x _ => abs_add_le (f x) (g x))
  simp only [Pi.add_apply] at hh
  rw [integral_add hf.abs hg.abs] at hh
  simpa only [mul_add] using mul_le_mul_of_nonneg_left hh (one_div_nonneg.mpr hX.le)

theorem profileSum_mean_le (X s Y B : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (outer : Bool) (n : ℕ) (hX : 0 < X)
    (hb : ∀ js ∈ selectedProfiles s outer n,
      (1/X)*(∫ x in Icc X (2*X),
        |profileKernel X s P z outer js (floorKernel (x-x*(Y/X)) x)|) ≤ B) :
    (1/X)*(∫ x in Icc X (2*X),
      |∑ js ∈ selectedProfiles s outer n,
        profileKernel X s P z outer js (floorKernel (x-x*(Y/X)) x)|) ≤
      ((selectedProfiles s outer n).card:ℝ)*B := by
  apply (absolute_sum_mean_le (selectedProfiles s outer n)
    (fun js x => profileKernel X s P z outer js (floorKernel (x-x*(Y/X)) x)) X hX
    (fun js _ => profile_moving_integrable X s Y P z outer js)).trans
  simpa using Finset.sum_le_sum hb

theorem higherBand_moving_integrable (X s Y : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (hs : 0 < s) (hg : BandGeometry X s P z) :
    IntegrableOn (fun x => higherBand X s P z (floorKernel (x-x*(Y/X)) x))
      (Icc X (2*X)) := by
  simp_rw [higherBand_eq_profiles X s P z hs hg]
  exact (integrable_finsetSum _ (fun js _ => profile_moving_integrable X s Y P z true js)).sub
    (integrable_finsetSum _ (fun js _ => profile_moving_integrable X s Y P z false js))

def bandProfileCost (s : ℝ) : ℝ :=
  ((selectedProfiles s true 4).card:ℝ) + ((selectedProfiles s false 3).card:ℝ)

theorem eventually_higherBand_absolute_log (s : ℝ) (A : ℕ)
    (hs : 0 < s) (hs1 : s ≤ 1/1000) :
    ∀ᶠ X : ℝ in atTop, 1 < X ∧ 1000 ≤ Real.log X ∧
      ∀ (P : Finset ℕ) (z : ℝ → ℝ), BandGeometry X s P z →
        let Y := halfWidth X (101/1000)
        (1/X)*(∫ x in Icc X (2*X),
          |higherBand X s P z (floorKernel (x-x*(Y/X)) x)|) ≤
          bandProfileCost s*Y/(Real.log X)^A := by
  let J := selectedProfiles s true 4 ∪ selectedProfiles s false 3
  have hall : ∀ᶠ X : ℝ in atTop, ∀ js ∈ J,
      ∀ (P : Finset ℕ) (z : ℝ → ℝ) (outer : Bool), BandGeometry X s P z →
        (1/X)*(∫ x in Icc X (2*X), |profileKernel X s P z outer js
          (floorKernel (x-x*(halfWidth X (101/1000)/X)) x)|) ≤
          halfWidth X (101/1000)/(Real.log X)^A := by
    apply (eventually_all_finset J).mpr
    intro js hjs
    have hlen : 3 ≤ js.length := by
      rcases Finset.mem_union.mp hjs with ho | hi
      · have hh := (Finset.mem_filter.mp ho).2; omega
      · exact (Finset.mem_filter.mp hi).2
    filter_upwards [eventually_profile_absolute_log s A hs hs1 (js.length-1) (by omega)]
      with X hm
    intro P z outer hg
    exact hm.2.2 P z outer js (by omega) hg
  filter_upwards [hall, eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1000)] with X hm hX hlog
  refine ⟨hX,hlog,?_⟩
  intro P z hg
  dsimp only
  let Y := halfWidth X (101/1000)
  let fo : ℝ → ℝ := fun x => ∑ js ∈ selectedProfiles s true 4,
    profileKernel X s P z true js (floorKernel (x-x*(Y/X)) x)
  let fi : ℝ → ℝ := fun x => ∑ js ∈ selectedProfiles s false 3,
    profileKernel X s P z false js (floorKernel (x-x*(Y/X)) x)
  have ho := profileSum_mean_le X s Y (Y/(Real.log X)^A) P z true 4 (by linarith)
    (fun js hjs => hm js (Finset.mem_union_left _ hjs) P z true hg)
  have hi := profileSum_mean_le X s Y (Y/(Real.log X)^A) P z false 3 (by linarith)
    (fun js hjs => hm js (Finset.mem_union_right _ hjs) P z false hg)
  have hfo : IntegrableOn fo (Icc X (2*X)) :=
    integrable_finsetSum _ (fun js _ => profile_moving_integrable X s Y P z true js)
  have hfi : IntegrableOn fi (Icc X (2*X)) :=
    integrable_finsetSum _ (fun js _ => profile_moving_integrable X s Y P z false js)
  simp_rw [higherBand_eq_profiles X s P z hs hg]
  apply (absolute_sub_mean_le fo fi X (by linarith) hfo hfi).trans
  calc
    _ ≤ ((selectedProfiles s true 4).card:ℝ)*(Y/(Real.log X)^A) +
        ((selectedProfiles s false 3).card:ℝ)*(Y/(Real.log X)^A) := add_le_add ho hi
    _ = _ := by unfold bandProfileCost; ring

/-- Absolute first mean for the actual complete higher sector, both prime
bands, retaining all signs, weights, profiles and representation collisions. -/
theorem eventually_higher_absolute_log (s : ℝ) (A : ℕ)
    (hs : 0 < s) (hs1 : s ≤ 1/1000) :
    ∀ᶠ X : ℝ in atTop, 1 < X ∧ 1000 ≤ Real.log X ∧
      let Y := halfWidth X (101/1000)
      (1/X)*(∫ x in Icc X (2*X), |higherRemainder X s (x-x*(Y/X)) x|) ≤
        (2*bandProfileCost s)*Y/(Real.log X)^A := by
  filter_upwards [eventually_higherBand_absolute_log s A hs hs1] with X hm
  refine ⟨hm.1,hm.2.1,?_⟩
  dsimp only
  let Y := halfWidth X (101/1000)
  have hlarge := large_band_geometry X s hm.1 hs hs1 hm.2.1
  have hsmall := small_band_geometry X s hm.1 hs hs1 hm.2.1
  have ha := hm.2.2 (largePrimes X) (cutoffThree X s) hlarge
  have hb := hm.2.2 (smallPrimes X s) (cappedFourth X s) hsmall
  unfold higherRemainder
  apply (absolute_add_mean_le
    (fun x => higherBand X s (largePrimes X) (cutoffThree X s) (floorKernel (x-x*(Y/X)) x))
    (fun x => higherBand X s (smallPrimes X s) (cappedFourth X s) (floorKernel (x-x*(Y/X)) x))
    X (by linarith [hm.1])
    (higherBand_moving_integrable X s Y _ _ hs hlarge)
    (higherBand_moving_integrable X s Y _ _ hs hsmall)).trans
  calc
    _ ≤ bandProfileCost s*Y/(Real.log X)^A + bandProfileCost s*Y/(Real.log X)^A :=
      add_le_add ha hb
    _ = _ := by ring

/-- Absorb the fixed profile count into one extra logarithmic power. -/
theorem eventually_higher_absolute_log_unit (s : ℝ) (A : ℕ)
    (hs : 0 < s) (hs1 : s ≤ 1/1000) :
    ∀ᶠ X : ℝ in atTop, 1 < X ∧ 1000 ≤ Real.log X ∧
      let Y := halfWidth X (101/1000)
      (1/X)*(∫ x in Icc X (2*X), |higherRemainder X s (x-x*(Y/X)) x|) ≤
        Y/(Real.log X)^A := by
  filter_upwards [eventually_higher_absolute_log s (A+1) hs hs1,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2*bandProfileCost s)),
    halfWidth_eventually (101/1000) (by norm_num)] with X hm hcost hY
  refine ⟨hm.1,hm.2.1,hm.2.2.trans ?_⟩
  have hl : 0 < Real.log X := Real.log_pos hm.1
  apply (div_le_div_iff₀ (pow_pos hl (A+1)) (pow_pos hl A)).mpr
  rw [pow_succ]
  have hh := mul_le_mul_of_nonneg_left hcost
    (mul_nonneg hY.1.le (pow_nonneg hl.le A))
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hh

#print axioms higherBand_eq_profiles
#print axioms eventually_higher_absolute_log
#print axioms eventually_higher_absolute_log_unit
run_cmd do
  for decl in [``selectedKernel_eq_profiles, ``higherBand_eq_profiles,
      ``profile_moving_integrable, ``absolute_sum_mean_le, ``absolute_sub_mean_le,
      ``absolute_add_mean_le, ``profileSum_mean_le, ``higherBand_moving_integrable,
      ``eventually_higherBand_absolute_log, ``eventually_higher_absolute_log,
      ``eventually_higher_absolute_log_unit] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end LongerTupleHigherMeanWork
