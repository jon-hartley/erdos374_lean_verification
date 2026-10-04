import ShortPairProfileFirstMeanWork

/-! Exact short-pair assembly and its complete literal absolute mean. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ShortPairMeanWork
open ShortPairProfilesWork ShortPairSplitWork ShortPairProfileFirstMeanWork
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

theorem shortPairBand_split (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (f : ℕ → ℝ) :
    shortPairBand X s P z f = branchBand X s P z true f + branchBand X s P z false f := by
  unfold shortPairBand branchBand selectedKernel
  simp only [↓reduceIte,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro p _
  apply Finset.sum_congr rfl; intro d _
  simp only [Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro t _
  by_cases hlen : t.length=2
  · obtain ⟨u,v,rfl⟩ := List.length_eq_two.mp hlen
    by_cases hv : (v:ℝ)≤X^(8/35:ℝ) <;> by_cases hu : (u:ℝ)≤X^(8/35:ℝ) <;>
      simp [chosen,ShortPairSplitWork.prime,ShortPairSplitWork.drop,pair_short_choice,hv,hu]
  · simp [hlen]

theorem shortPairBand_eq_profiles (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (hs : 0<s) (hg : BandGeometry X s P z) (f : ℕ → ℝ) :
    shortPairBand X s P z f =
      (∑ js∈pairProfiles s,pairKernel X s P z true js f) +
      ∑ js∈pairProfiles s,pairKernel X s P z false js f := by
  rw [shortPairBand_split,branchBand_eq_profiles X s P z true hs hg,
    branchBand_eq_profiles X s P z false hs hg]

theorem pair_moving_integrable (X s Y : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) :
    IntegrableOn (fun x => pairKernel X s P z second js
      (floorKernel (x-x*(Y/X)) x)) (Icc X (2*X)) := by
  simp_rw [ShortPairProfileFirstMeanWork.profile_eq_remainder]
  simpa only [mul_div_assoc] using TailRemainderBand.moving_remainder_integrable
    (ShortPairProfileFirstMeanWork.divisorSupport X s P z second js)
    (ShortPairProfileFirstMeanWork.divisorCoefficient X s P z second js) X Y

theorem pairSum_mean_le (X s Y B : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (hX : 0<X)
    (hb : ∀ js∈pairProfiles s,
      (1/X)*(∫ x in Icc X (2*X), |pairKernel X s P z second js
        (floorKernel (x-x*(Y/X)) x)|) ≤ B) :
    (1/X)*(∫ x in Icc X (2*X), |∑ js∈pairProfiles s,
      pairKernel X s P z second js (floorKernel (x-x*(Y/X)) x)|) ≤
      ((pairProfiles s).card:ℝ)*B := by
  apply (absolute_sum_mean_le (pairProfiles s)
    (fun js x => pairKernel X s P z second js (floorKernel (x-x*(Y/X)) x)) X hX
    (fun js _ => pair_moving_integrable X s Y P z second js)).trans
  simpa using Finset.sum_le_sum hb

theorem shortPairBand_moving_integrable (X s Y : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (hs : 0<s) (hg : BandGeometry X s P z) :
    IntegrableOn (fun x => shortPairBand X s P z (floorKernel (x-x*(Y/X)) x))
      (Icc X (2*X)) := by
  simp_rw [shortPairBand_eq_profiles X s P z hs hg]
  exact (integrable_finsetSum _ (fun js _ => pair_moving_integrable X s Y P z true js)).add
    (integrable_finsetSum _ (fun js _ => pair_moving_integrable X s Y P z false js))

theorem eventually_shortPairBand_absolute_log (s : ℝ) (A : ℕ)
    (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ 1000≤Real.log X ∧
      ∀ (P : Finset ℕ) (z : ℝ → ℝ), BandGeometry X s P z →
        let Y := halfWidth X (101/1000)
        (1/X)*(∫ x in Icc X (2*X), |shortPairBand X s P z
          (floorKernel (x-x*(Y/X)) x)|) ≤
          (2*((pairProfiles s).card:ℝ))*Y/(Real.log X)^A := by
  filter_upwards [eventually_pair_absolute_log s A hs hs1] with X hm
  refine ⟨hm.1,hm.2.1,?_⟩
  intro P z hg
  dsimp only
  let Y := halfWidth X (101/1000)
  have hb (second : Bool) := pairSum_mean_le X s Y (Y/(Real.log X)^A) P z second
    (by linarith [hm.1]) (fun js hjs => hm.2.2 P z second js
      (Finset.mem_filter.mp hjs).2 hg)
  simp_rw [shortPairBand_eq_profiles X s P z hs hg]
  apply (absolute_add_mean_le
    (fun x => ∑ js∈pairProfiles s,pairKernel X s P z true js (floorKernel (x-x*(Y/X)) x))
    (fun x => ∑ js∈pairProfiles s,pairKernel X s P z false js (floorKernel (x-x*(Y/X)) x))
    X (by linarith [hm.1])
    (integrable_finsetSum _ (fun js _ => pair_moving_integrable X s Y P z true js))
    (integrable_finsetSum _ (fun js _ => pair_moving_integrable X s Y P z false js))).trans
  calc
    _ ≤ ((pairProfiles s).card:ℝ)*(Y/(Real.log X)^A) +
        ((pairProfiles s).card:ℝ)*(Y/(Real.log X)^A) := add_le_add (hb true) (hb false)
    _ = _ := by ring

theorem eventually_shortPair_absolute_log (s : ℝ) (A : ℕ)
    (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ 1000≤Real.log X ∧
      let Y := halfWidth X (101/1000)
      (1/X)*(∫ x in Icc X (2*X), |shortPairRemainder X s (x-x*(Y/X)) x|) ≤
        (4*((pairProfiles s).card:ℝ))*Y/(Real.log X)^A := by
  filter_upwards [eventually_shortPairBand_absolute_log s A hs hs1] with X hm
  refine ⟨hm.1,hm.2.1,?_⟩
  dsimp only
  let Y := halfWidth X (101/1000)
  have hlarge := large_band_geometry X s hm.1 hs hs1 hm.2.1
  have hsmall := small_band_geometry X s hm.1 hs hs1 hm.2.1
  have ha := hm.2.2 (largePrimes X) (cutoffThree X s) hlarge
  have hb := hm.2.2 (smallPrimes X s) (cappedFourth X s) hsmall
  unfold shortPairRemainder
  apply (absolute_add_mean_le
    (fun x => shortPairBand X s (largePrimes X) (cutoffThree X s) (floorKernel (x-x*(Y/X)) x))
    (fun x => shortPairBand X s (smallPrimes X s) (cappedFourth X s) (floorKernel (x-x*(Y/X)) x))
    X (by linarith [hm.1])
    (shortPairBand_moving_integrable X s Y _ _ hs hlarge)
    (shortPairBand_moving_integrable X s Y _ _ hs hsmall)).trans
  calc
    _ ≤ (2*((pairProfiles s).card:ℝ))*Y/(Real.log X)^A +
        (2*((pairProfiles s).card:ℝ))*Y/(Real.log X)^A := add_le_add ha hb
    _ = _ := by ring

/-- Complete short-pair sector, with the fixed profile cost absorbed by one
extra logarithmic power. Both prime bands and all collisions are retained. -/
theorem eventually_shortPair_absolute_log_unit (s : ℝ) (A : ℕ)
    (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ 1000≤Real.log X ∧
      let Y := halfWidth X (101/1000)
      (1/X)*(∫ x in Icc X (2*X), |shortPairRemainder X s (x-x*(Y/X)) x|) ≤
        Y/(Real.log X)^A := by
  filter_upwards [eventually_shortPair_absolute_log s (A+1) hs hs1,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4*((pairProfiles s).card:ℝ))),
    halfWidth_eventually (101/1000) (by norm_num)] with X hm hcost hY
  refine ⟨hm.1,hm.2.1,hm.2.2.trans ?_⟩
  have hl : 0<Real.log X := Real.log_pos hm.1
  apply (div_le_div_iff₀ (pow_pos hl (A+1)) (pow_pos hl A)).mpr
  rw [pow_succ]
  have hh := mul_le_mul_of_nonneg_left hcost
    (mul_nonneg hY.1.le (pow_nonneg hl.le A))
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hh

#print axioms shortPairBand_eq_profiles
#print axioms eventually_shortPair_absolute_log_unit
run_cmd do
  for decl in [``branchBand_eq_profiles, ``shortPairBand_split, ``shortPairBand_eq_profiles,
      ``pair_moving_integrable, ``pairSum_mean_le, ``shortPairBand_moving_integrable,
      ``eventually_shortPairBand_absolute_log, ``eventually_shortPair_absolute_log,
      ``eventually_shortPair_absolute_log_unit] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end ShortPairMeanWork
