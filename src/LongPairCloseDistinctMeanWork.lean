import LongPairDistinctMultiplicityWork
import SparseFloorVariableMeanWork
import Mathlib.Data.Nat.Dist

/-! Distinct tuple primes within X^.18 of one another give a sparse
representation family. Its complete absolute mean has a power saving;
the exact farther-apart complement is retained. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LongPairCloseDistinctMeanWork
open LongerTupleEncoding LongerTupleActualProfiles ShortPairSplitWork
open LongPairRepeatedCoreMeanWork LongPairDistinctCoreWork LongPairDistinctMultiplicityWork
open UpperAfter545Remaining

def tupleGap (r : Representation) : ℕ := Nat.dist (prime false r) (prime true r)
def closeSource (X s : ℝ) : Finset Representation :=
  (distinctSource X s).filter (fun r => (tupleGap r:ℝ)≤X^(9/50:ℝ))
def separatedSource (X s : ℝ) : Finset Representation :=
  (distinctSource X s).filter (fun r => X^(9/50:ℝ)<(tupleGap r:ℝ))
def closeRemainder (X s L R : ℝ) : ℝ :=
  (∑ r∈closeSource X s,originalWeight X s true r*
    (floorKernel L R (LongerTupleEncoding.index r):ℂ)).re
def separatedRemainder (X s L R : ℝ) : ℝ :=
  (∑ r∈separatedSource X s,originalWeight X s true r*
    (floorKernel L R (LongerTupleEncoding.index r):ℂ)).re

theorem distinct_partition (X s L R : ℝ) :
    distinctRemainder X s L R=closeRemainder X s L R+separatedRemainder X s L R := by
  unfold distinctRemainder closeRemainder separatedRemainder closeSource separatedSource
  rw [←Complex.add_re]
  congr 1
  simp only [Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rcases le_or_gt (tupleGap r:ℝ) (X^(9/50:ℝ)) with hh | hh <;> simp [hh,not_lt_of_ge,not_le_of_gt]

theorem close_card_bound (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) :
    ((closeSource X s).card:ℝ)≤24*X^(371/500:ℝ) := by
  let P := Finset.range (Nat.floor (X^(313/1000:ℝ))+1)
  let D := Finset.range (Nat.floor (X^(1/1000:ℝ))+1)
  let Q := Finset.range (Nat.floor (X^(31/125:ℝ))+1)
  let H := Nat.floor (X^(9/50:ℝ))
  let F := P ×ˢ (D ×ˢ Q)
  let C := F.biUnion (fun u : PairRep =>
    (Finset.Icc (u.2.2-H) (u.2.2+H)).image (fun b => (u.1,u.2.1,[u.2.2,b])))
  have hsub : closeSource X s⊆C := by
    intro r hr
    obtain ⟨hr,hgap⟩ := Finset.mem_filter.mp hr
    obtain ⟨a,b,he,_,_,_,_,_,_⟩ := source_prime_shape X s hX hs hs1 hlog r hr
    have hf := source_factor_ranges X s hX hs hs1 hlog r hr
    have hd := source_small_divisor_power X s hX hs hs1 hlog r hr
    have hp : (r.1:ℝ)≤X^(313/1000:ℝ) := hf.2.1.le.trans
      (Real.rpow_le_rpow_of_exponent_le hX.le (by linarith))
    have hD : (r.2.1:ℝ)≤X^(1/1000:ℝ) := hd.2.le.trans
      (Real.rpow_le_rpow_of_exponent_le hX.le hs1)
    have hQ : (a:ℝ)≤X^(31/125:ℝ) := (hf.2.2 a (by simp [he])).2.2.le.trans
      (Real.rpow_le_rpow_of_exponent_le hX.le (by linarith))
    have hu : (r.1,r.2.1,a)∈F := by
      simp only [F,P,D,Q,Finset.mem_product,Finset.mem_range,Nat.lt_add_one_iff]
      exact ⟨(Nat.le_floor_iff (by positivity)).mpr hp,
        (Nat.le_floor_iff (by positivity)).mpr hD,(Nat.le_floor_iff (by positivity)).mpr hQ⟩
    have hdist : Nat.dist a b≤H := by
      apply Nat.le_floor
      simpa [tupleGap,prime,he] using hgap
    have hb : b∈Finset.Icc (a-H) (a+H) := by
      rw [Finset.mem_Icc]
      unfold Nat.dist at hdist
      omega
    exact Finset.mem_biUnion.mpr ⟨(r.1,r.2.1,a),hu,
      Finset.mem_image.mpr ⟨b,hb,by change (r.1,r.2.1,[a,b])=r; rw [←he]⟩⟩
  have hc : (closeSource X s).card≤F.card*(2*H+1) := by
    calc
      _ ≤ C.card := Finset.card_le_card hsub
      _ ≤ ∑ u∈F,((Finset.Icc (u.2.2-H) (u.2.2+H)).image
          (fun b => (u.1,u.2.1,[u.2.2,b]))).card := Finset.card_biUnion_le
      _ ≤ ∑ _u∈F,(2*H+1) := Finset.sum_le_sum (fun u _ => by
        apply Finset.card_image_le.trans
        rw [Nat.card_Icc]
        omega)
      _ = F.card*(2*H+1) := by simp
  have hfactor (e : ℝ) (he : 0≤e) : ((Nat.floor (X^e)+1:ℕ):ℝ)≤2*X^e := by
    have hf := Nat.floor_le (Real.rpow_nonneg (by linarith : 0≤X) e)
    have hone := Real.one_le_rpow hX.le he
    push_cast
    linarith
  have hH : ((2*H+1:ℕ):ℝ)≤3*X^(9/50:ℝ) := by
    have hh := Nat.floor_le (by positivity : 0≤X^(9/50:ℝ))
    have hone := Real.one_le_rpow hX.le (by norm_num : (0:ℝ)≤9/50)
    dsimp [H]
    push_cast
    linarith
  have hXp : 0<X := by linarith
  calc
    _ ≤ (F.card:ℝ)*(2*H+1:ℕ) := by exact_mod_cast hc
    _ = (((Nat.floor (X^(313/1000:ℝ))+1:ℕ):ℝ)*
        (((Nat.floor (X^(1/1000:ℝ))+1:ℕ):ℝ)*
          ((Nat.floor (X^(31/125:ℝ))+1:ℕ):ℝ)))*((2*H+1:ℕ):ℝ) := by
      simp only [F,P,D,Q,Finset.card_product,Finset.card_range,Nat.cast_mul]
    _ ≤ ((2*X^(313/1000:ℝ))*((2*X^(1/1000:ℝ))*(2*X^(31/125:ℝ))))*
        (3*X^(9/50:ℝ)) := by
      gcongr
      · exact hfactor _ (by norm_num)
      · exact hfactor _ (by norm_num)
      · exact hfactor _ (by norm_num)
    _ = 24*(X^(313/1000:ℝ)*X^(1/1000:ℝ)*X^(31/125:ℝ)*X^(9/50:ℝ)) := by ring
    _ = 24*X^(371/500:ℝ) := by
      rw [←Real.rpow_add hXp,←Real.rpow_add hXp,←Real.rpow_add hXp]
      norm_num

theorem eventually_close_card (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop,1<X ∧ 1000≤Real.log X ∧
      ((closeSource X s).card:ℝ)≤X^(3711/5000:ℝ) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1000),
    PolynomialLogEnvelope.eventually_constant_bound 24 (1/5000)
      (by norm_num) (by norm_num)] with X hX hlog hc
  refine ⟨hX,hlog,(close_card_bound X s hX hs hs1 hlog).trans ?_⟩
  calc
    _ ≤ X^(1/5000:ℝ)*X^(371/500:ℝ) := mul_le_mul_of_nonneg_right hc.2 (by positivity)
    _ = _ := by rw [←Real.rpow_add (by linarith : 0<X)]; norm_num

/-- Absolute-inside-integral saving for the complete close distinct piece,
uniformly in the moving width. -/
theorem eventually_close_absolute_power (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop,1<X ∧ 1000≤Real.log X ∧ ∀ Y : ℝ,0≤Y → Y≤X/2 →
      (1/X)*(∫ x in Icc X (2*X),|closeRemainder X s (x-x*(Y/X)) x|)≤
        Y*X^(-1/2500:ℝ) := by
  filter_upwards [eventually_close_card s hs hs1,
    SparseFloorVariableMeanWork.eventually_sparse_absolute (α:=Representation)
      (3711/5000) (26/35) (1/2500) (by norm_num) (by norm_num) (by norm_num)] with X hc hm
  refine ⟨hc.1,hc.2.1,?_⟩
  intro Y hY hYX
  have hb := hm.2 (closeSource X s) LongerTupleEncoding.index
    (fun r => (originalWeight X s true r).re) Y hc.2.2
    (by intro r hr
        have hsupp : LongerTupleEncoding.index r∈LongPairDistinctCoreWork.coreSupport X s :=
          Finset.mem_image.mpr ⟨r,(Finset.mem_filter.mp hr).1,rfl⟩
        exact (support_geometry X s hc.1 hs hs1 hc.2.1 _ hsupp).1.le)
    (fun r _ => (Complex.abs_re_le_norm _).trans (originalWeight_norm_le X s true r)) hY hYX
  simpa only [closeRemainder,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero,neg_div] using hb

theorem eventually_close_absolute_log_unit (s : ℝ) (A : ℕ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop,1<X ∧ 1000≤Real.log X ∧
      let Y := PositiveSharpPowerWindow.halfWidth X (101/1000)
      (1/X)*(∫ x in Icc X (2*X),|closeRemainder X s (x-x*(Y/X)) x|)≤Y/(Real.log X)^A := by
  filter_upwards [eventually_close_absolute_power s hs hs1,
    PolynomialLogEnvelope.eventually_bound 1 A (1/2500) (by norm_num) (by norm_num),
    PositiveSharpPowerWindow.halfWidth_eventually (101/1000) (by norm_num)] with X hb he hY
  refine ⟨hb.1,hb.2.1,(hb.2.2 _ hY.1.le (by linarith [hY.2])).trans ?_⟩
  have hl : 0<Real.log X := Real.log_pos hb.1
  have hXp : 0<X := by linarith [hb.1]
  have hlog : (Real.log X)^A≤X^(1/2500:ℝ) := by
    apply le_trans _ he.2
    simp only [one_mul]
    exact pow_le_pow_left₀ hl.le (by linarith) A
  apply (le_div_iff₀ (pow_pos hl A)).mpr
  have hunit : X^(-1/2500:ℝ)*(Real.log X)^A≤1 := by
    calc
      _ ≤ X^(-1/2500:ℝ)*X^(1/2500:ℝ) := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = 1 := by rw [←Real.rpow_add hXp]; norm_num
  have hh := mul_le_mul_of_nonneg_left hunit hY.1.le
  simpa only [mul_assoc,mul_one] using hh

#print axioms eventually_close_absolute_power
#print axioms eventually_close_absolute_log_unit
run_cmd do
  for decl in [``distinct_partition, ``close_card_bound, ``eventually_close_card,
      ``eventually_close_absolute_power, ``eventually_close_absolute_log_unit] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end LongPairCloseDistinctMeanWork
