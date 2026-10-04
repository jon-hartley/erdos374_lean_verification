import SeparatedCoreOffDiagonalWork

/-! Distinct nearby completed products cannot share any original large
prime. The signed off-diagonal coefficients can therefore be expanded
using only pairs of representations with disjoint large-prime lists. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace SeparatedCoreSharedPrimeWork
open LongerTupleEncoding LongPairCloseDistinctMeanWork LongPairSeparatedCoreWork
open SeparatedCoreGlobalPerronWork SeparatedCoreCorrelationWork PositiveSharpPowerWindow

def largeFactors (r : Representation) : List ℕ := r.1 :: r.2.2

def disjointLarge (r r' : Representation) : Prop :=
  ∀ q∈largeFactors r, q∉largeFactors r'

theorem common_divisor_gap (q n m : ℕ) (hn : q∣n) (hm : q∣m) (hne : n≠m) :
    (q:ℝ)≤|(n:ℝ)-m| := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hd : q≤m-n := Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) (Nat.dvd_sub hm hn)
    have hc : (q:ℝ)≤(m:ℝ)-n := by
      have hh : (q:ℝ)≤(m-n:ℕ) := by exact_mod_cast hd
      rwa [Nat.cast_sub hlt.le] at hh
    have hnm : (n:ℝ)≤m := by exact_mod_cast hlt.le
    rw [abs_of_nonpos (by linarith : (n:ℝ)-m≤0)]
    linarith
  · have hd : q≤n-m := Nat.le_of_dvd (Nat.sub_pos_of_lt hgt) (Nat.dvd_sub hn hm)
    have hc : (q:ℝ)≤(n:ℝ)-m := by
      have hh : (q:ℝ)≤(n-m:ℕ) := by exact_mod_cast hd
      rwa [Nat.cast_sub hgt.le] at hh
    have hmn : (m:ℝ)≤n := by exact_mod_cast hgt.le
    rw [abs_of_nonneg (by linarith : 0≤(n:ℝ)-m)]
    exact hc

theorem largeFactor_dvd (r : Representation) (q : ℕ) (hq : q∈largeFactors r) :
    q∣index r := by
  rcases List.mem_cons.mp hq with he | hq
  · subst q
    exact dvd_mul_of_dvd_left (dvd_mul_right r.1 r.2.1) _
  · exact dvd_mul_of_dvd_right (List.dvd_prod hq) _

theorem largeFactor_lower (X s : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hlog : 1000≤Real.log X) (r : Representation) (hr : r∈separatedSource X s)
    (q : ℕ) (hq : q∈largeFactors r) : X^(229/1000 : ℝ)≤(q:ℝ) := by
  have hh := source_factor_ranges X s hX hs hs1 hlog r hr
  rcases List.mem_cons.mp hq with he | hq
  · subst q
    exact (Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num : (229/1000:ℝ)≤9/35)).trans hh.1
  · exact (hh.2.2 q hq).2.1.le

theorem nearby_representations_disjoint (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X)
    (n m : ℕ) (hne : n≠m) (hgap : |(n:ℝ)-m|<2*halfWidth X (101/1000))
    (r r' : Representation) (hr : r∈separatedSource X s) (hr' : r'∈separatedSource X s)
    (hn : index r∣n) (hm : index r'∣m) : disjointLarge r r' := by
  intro q hq hq'
  have hd := common_divisor_gap q n m ((largeFactor_dvd r q hq).trans hn)
    ((largeFactor_dvd r' q hq').trans hm) hne
  have hl := largeFactor_lower X s hX hs hs1 hlog r hr q hq
  have he : 2*halfWidth X (101/1000)≤X^(229/1000 : ℝ) := by
    unfold halfWidth
    have hh := Real.rpow_le_rpow_of_exponent_le hX.le
      (by norm_num : (101/1000:ℝ)≤229/1000)
    linarith
  linarith

theorem shared_largeFactor_overlap_zero (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X)
    (hY : halfWidth X (101/1000)<X)
    (n m : ℕ) (hne : n≠m) (r r' : Representation)
    (hr : r∈separatedSource X s) (hr' : r'∈separatedSource X s)
    (hn : index r∣n) (hm : index r'∣m) (q : ℕ)
    (hq : q∈largeFactors r) (hq' : q∈largeFactors r') :
    MovingWindowCorrelationWork.overlap X (halfWidth X (101/1000)/X) n m=0 := by
  have hXp : 0<X := by linarith
  apply MovingWindowCorrelationWork.overlap_zero_of_separated X _ n m hXp
    (by unfold halfWidth; positivity) hY
  by_contra hh
  exact nearby_representations_disjoint X s hX hs hs1 hlog n m hne (lt_of_not_ge hh)
    r r' hr hr' hn hm q hq hq'

theorem coefficient_product_eq_disjoint (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X)
    (n m : ℕ) (hne : n≠m) (hgap : |(n:ℝ)-m|<2*halfWidth X (101/1000)) :
    physicalCoefficient X s n * physicalCoefficient X s m =
      ∑ r∈separatedSource X s, ∑ r'∈separatedSource X s,
        if index r∣n ∧ index r'∣m ∧ disjointLarge r r' then
          LongPairCofactorSwitchWork.realWeight X s r * LongPairCofactorSwitchWork.realWeight X s r'
        else 0 := by
  rw [physicalCoefficient_eq_source, physicalCoefficient_eq_source, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r' hr'
  by_cases hn : index r∣n
  · by_cases hm : index r'∣m
    · have hd := nearby_representations_disjoint X s hX hs hs1 hlog n m hne hgap r r' hr hr' hn hm
      simp [hn,hm,hd]
    · simp [hn,hm]
  · simp [hn]

#print axioms coefficient_product_eq_disjoint
run_cmd do
  for decl in [``common_divisor_gap, ``largeFactor_dvd, ``largeFactor_lower,
      ``nearby_representations_disjoint, ``shared_largeFactor_overlap_zero,
      ``coefficient_product_eq_disjoint] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end SeparatedCoreSharedPrimeWork
