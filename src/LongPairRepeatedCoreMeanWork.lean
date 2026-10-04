import SparseFloorMeanWork
import LongPairTwoSidedCoreWork

/-! The repeated-prime part of the literal two-sided core is sparse
enough for an unconditional absolute first mean. Its distinct-prime
complement is retained exactly and is not estimated. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LongPairRepeatedCoreMeanWork
open LongerTupleEncoding LongerTupleActualProfiles LongPairTwoSidedCoreMeanWork
open LongPairTwoSidedCoreWork ShortPairSplitWork SieveWeightedCutoffs PositiveSharpBoxedCount
open UpperAfter545Remaining

def repeatedSource (X s : ℝ) : Finset Representation :=
  (twoSidedCoreSource X s).filter (fun r => prime false r=prime true r)
def distinctSource (X s : ℝ) : Finset Representation :=
  (twoSidedCoreSource X s).filter (fun r => prime false r≠prime true r)
def repeatedRemainder (X s L R : ℝ) : ℝ :=
  (∑ r∈repeatedSource X s,
    originalWeight X s true r*(floorKernel L R (LongerTupleEncoding.index r):ℂ)).re
def distinctRemainder (X s L R : ℝ) : ℝ :=
  (∑ r∈distinctSource X s,
    originalWeight X s true r*(floorKernel L R (LongerTupleEncoding.index r):ℂ)).re

theorem source_length (X s : ℝ) (r : Representation) (hr : r∈twoSidedCoreSource X s) :
    r.2.2.length=2 := by
  exact ((LongPairCollectionWork.mem_source X s _ _ r).mp
    (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1).1).2.2.2.1

theorem repeated_shape (X s : ℝ) (r : Representation) (hr : r∈repeatedSource X s) :
    ∃ q : ℕ,r.2.2=[q,q] := by
  obtain ⟨hc,heq⟩ := Finset.mem_filter.mp hr
  obtain ⟨a,b,he⟩ := List.length_eq_two.mp (source_length X s r hc)
  have hab : a=b := by simpa [prime,he] using heq
  exact ⟨a,by simpa only [←hab] using he⟩

def projection (r : Representation) : PairRep := (r.1,r.2.1,prime false r)

theorem projection_injOn (X s : ℝ) : Set.InjOn projection (repeatedSource X s : Set Representation) := by
  intro r hr t ht he
  obtain ⟨q,hq⟩ := repeated_shape X s r hr
  obtain ⟨a,ha⟩ := repeated_shape X s t ht
  have hp := congrArg Prod.fst he
  have hd := congrArg (fun u : PairRep => u.2.1) he
  have hprime := congrArg (fun u : PairRep => u.2.2) he
  change r.1=t.1 at hp
  change r.2.1=t.2.1 at hd
  have hqa : q=a := by simpa [projection,prime,hq,ha] using hprime
  apply Prod.ext hp
  apply Prod.ext hd
  rw [hq,ha,hqa]

theorem projection_bounds (X s : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hlog : 1000≤Real.log X) (r : Representation) (hr : r∈repeatedSource X s) :
    (r.1:ℝ)≤X^(1/3:ℝ) ∧ (r.2.1:ℝ)≤X^(1/100:ℝ) ∧
      (prime false r:ℝ)≤X^(1/4:ℝ) := by
  have hc := (Finset.mem_filter.mp hr).1
  have hcol := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1).1
  obtain ⟨hp,hd,_,_,_,_⟩ := (LongPairCollectionWork.mem_source X s _ _ r).mp hcol
  have hg := large_band_geometry X s hX hs hs1 hlog r.1 hp
  have hf := source_factor_ranges X s hX hs hs1 hlog r hc
  have hX0 : 0<X := by linarith
  have hple : (r.1:ℝ)≤X^(1/3:ℝ) := hf.2.1.le.trans
    (Real.rpow_le_rpow_of_exponent_le hX.le (by linarith : (313/1000:ℝ)-3*s≤1/3))
  have hp1 : (1:ℝ)≤r.1 := by exact_mod_cast (by omega : 1≤r.1)
  have hlvl : 0≤level X s := by unfold level; exact Real.rpow_nonneg hX0.le _
  have hDle : level X s/(r.1:ℝ)≤X := by
    apply (div_le_self hlvl hp1).trans
    unfold level
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX.le
      (by linarith : 1-3*s≤(1:ℝ))
  have hdle := (PositiveSharpRemainderSupportGeometry.smallCarrier_lt _ s hg.2.2.1 hs
    (by linarith) r.2.1 hd).le.trans
    (Real.rpow_le_rpow (by linarith [hg.2.2.1] : 0≤level X s/(r.1:ℝ)) hDle hs.le)
  have hq := (hf.2.2 (prime false r)
    (prime_mem false r (source_length X s r hc))).2.2.le
  exact ⟨hple,hdle.trans (Real.rpow_le_rpow_of_exponent_le hX.le
    (by linarith : s≤(1/100:ℝ))),hq.trans (Real.rpow_le_rpow_of_exponent_le hX.le
      (by linarith : (26/105:ℝ)-s≤1/4))⟩

theorem repeated_card_bound (X s : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hlog : 1000≤Real.log X) :
    ((repeatedSource X s).card:ℝ)≤8*X^(89/150:ℝ) := by
  let P := Finset.range (Nat.floor (X^(1/3:ℝ))+1)
  let D := Finset.range (Nat.floor (X^(1/100:ℝ))+1)
  let Q := Finset.range (Nat.floor (X^(1/4:ℝ))+1)
  have hm : (repeatedSource X s).image projection ⊆ P ×ˢ (D ×ˢ Q) := by
    intro u hu
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hp,hd,hq⟩ := projection_bounds X s hX hs hs1 hlog r hr
    simp only [projection,Finset.mem_product,Finset.mem_range,Nat.lt_add_one_iff,P,D,Q]
    exact ⟨(Nat.le_floor_iff (by positivity)).mpr hp,
      (Nat.le_floor_iff (by positivity)).mpr hd,(Nat.le_floor_iff (by positivity)).mpr hq⟩
  have hc : (repeatedSource X s).card≤(P ×ˢ (D ×ˢ Q)).card := by
    rw [←Finset.card_image_of_injOn (projection_injOn X s)]
    exact Finset.card_le_card hm
  have hfactor (e : ℝ) (he : 0≤e) : ((Nat.floor (X^e)+1:ℕ):ℝ)≤2*X^e := by
    have hf := Nat.floor_le (Real.rpow_nonneg (by linarith : 0≤X) e)
    have hone := Real.one_le_rpow hX.le he
    push_cast
    linarith
  have hXp : 0<X := by linarith
  calc
    _ ≤ ((P ×ˢ (D ×ˢ Q)).card:ℝ) := by exact_mod_cast hc
    _ = ((Nat.floor (X^(1/3:ℝ))+1:ℕ):ℝ)*
        (((Nat.floor (X^(1/100:ℝ))+1:ℕ):ℝ)*((Nat.floor (X^(1/4:ℝ))+1:ℕ):ℝ)) := by
      simp only [P,D,Q,Finset.card_product,Finset.card_range,Nat.cast_mul]
    _ ≤ (2*X^(1/3:ℝ))*((2*X^(1/100:ℝ))*(2*X^(1/4:ℝ))) := by
      gcongr <;> apply hfactor <;> norm_num
    _ = 8*(X^(1/3:ℝ)*X^(1/100:ℝ)*X^(1/4:ℝ)) := by ring
    _ = 8*X^(89/150:ℝ) := by rw [←Real.rpow_add hXp,←Real.rpow_add hXp]; norm_num

theorem eventually_repeated_card (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop,1<X ∧ 1000≤Real.log X ∧
      ((repeatedSource X s).card:ℝ)≤X^(3/5:ℝ) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1000),
    PolynomialLogEnvelope.eventually_constant_bound 8 (1/150)
      (by norm_num) (by norm_num)] with X hX hlog hc
  refine ⟨hX,hlog,(repeated_card_bound X s hX hs hs1 hlog).trans ?_⟩
  calc
    _ ≤ X^(1/150:ℝ)*X^(89/150:ℝ) := mul_le_mul_of_nonneg_right hc.2 (by positivity)
    _ = X^(3/5:ℝ) := by rw [←Real.rpow_add (by linarith : 0<X)]; norm_num

theorem core_partition (X s L R : ℝ) :
    twoSidedCoreRemainder X s L R=repeatedRemainder X s L R+distinctRemainder X s L R := by
  unfold twoSidedCoreRemainder repeatedRemainder distinctRemainder repeatedSource distinctSource
  rw [←Complex.add_re]
  congr 1
  simp only [Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases he : prime false r=prime true r <;> simp [he]

theorem source_moving_integrable (S : Finset Representation) (X s Y : ℝ) :
    IntegrableOn (fun x => (∑ r∈S,originalWeight X s true r*
      (floorKernel (x-x*(Y/X)) x (LongerTupleEncoding.index r):ℂ)).re) (Icc X (2*X)) := by
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  exact integrable_finsetSum S (fun r _ =>
    (SparseFloorMeanWork.kernel_integrable (LongerTupleEncoding.index r) X Y).const_mul _)

theorem eventually_repeated_absolute_power (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop,1<X ∧ 1000≤Real.log X ∧
      let Y := PositiveSharpPowerWindow.halfWidth X (101/1000)
      (1/X)*(∫ x in Icc X (2*X),|repeatedRemainder X s (x-x*(Y/X)) x|)≤Y*X^(-1/10:ℝ) := by
  filter_upwards [eventually_repeated_card s hs hs1,
    SparseFloorMeanWork.eventually_sparse_absolute (α:=Representation),
    PositiveSharpPowerWindow.halfWidth_eventually (101/1000) (by norm_num)] with X hc hm hY
  refine ⟨hc.1,hc.2.1,?_⟩
  let Y := PositiveSharpPowerWindow.halfWidth X (101/1000)
  have hb := hm.2 (repeatedSource X s) LongerTupleEncoding.index
    (fun r => (originalWeight X s true r).re) Y hc.2.2
    (by intro r hr
        have hsupp : LongerTupleEncoding.index r∈coreSupport X s :=
          Finset.mem_image.mpr ⟨r,(Finset.mem_filter.mp hr).1,rfl⟩
        exact (support_geometry X s hc.1 hs hs1 hc.2.1 _ hsupp).1.le)
    (fun r _ => (Complex.abs_re_le_norm _).trans (originalWeight_norm_le X s true r))
    hY.1.le (by linarith [hY.2] : Y≤X/2)
  simpa only [repeatedRemainder,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] using hb

theorem eventually_repeated_absolute_log_unit (s : ℝ) (A : ℕ)
    (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop,1<X ∧ 1000≤Real.log X ∧
      let Y := PositiveSharpPowerWindow.halfWidth X (101/1000)
      (1/X)*(∫ x in Icc X (2*X),|repeatedRemainder X s (x-x*(Y/X)) x|)≤Y/(Real.log X)^A := by
  filter_upwards [eventually_repeated_absolute_power s hs hs1,
    PolynomialLogEnvelope.eventually_bound 1 A (1/10) (by norm_num) (by norm_num),
    PositiveSharpPowerWindow.halfWidth_eventually (101/1000) (by norm_num)] with X hb he hY
  refine ⟨hb.1,hb.2.1,hb.2.2.trans ?_⟩
  have hl : 0<Real.log X := Real.log_pos hb.1
  have hXp : 0<X := by linarith [hb.1]
  have hlog : (Real.log X)^A≤X^(1/10:ℝ) := by
    apply le_trans _ he.2
    simp only [one_mul]
    exact pow_le_pow_left₀ hl.le (by linarith) A
  apply (le_div_iff₀ (pow_pos hl A)).mpr
  have hunit : X^(-1/10:ℝ)*(Real.log X)^A≤1 := by
    calc
      _ ≤ X^(-1/10:ℝ)*X^(1/10:ℝ) :=
        mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hXp.le _)
      _ = 1 := by rw [←Real.rpow_add (by linarith [hb.1] : 0<X)]; norm_num
  have hh := mul_le_mul_of_nonneg_left hunit hY.1.le
  simpa only [mul_assoc,mul_one] using hh

#print axioms eventually_repeated_absolute_power
#print axioms eventually_repeated_absolute_log_unit
run_cmd do
  for decl in [``source_length, ``repeated_shape, ``projection_injOn,
      ``projection_bounds, ``repeated_card_bound, ``eventually_repeated_card,
      ``core_partition, ``source_moving_integrable,
      ``eventually_repeated_absolute_power, ``eventually_repeated_absolute_log_unit] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end LongPairRepeatedCoreMeanWork
