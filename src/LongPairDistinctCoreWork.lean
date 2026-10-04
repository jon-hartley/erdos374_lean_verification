import LongPairRepeatedCoreMeanWork
import RestDistinctCoreReductionWork

/-! The exact surviving distinct-prime divisor family. Its mean remains
open; all signed weights, collisions and source restrictions are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace LongPairDistinctCoreWork
open LongerTupleEncoding LongerTupleCollection LongerTupleActualProfiles
open LongPairRepeatedCoreMeanWork LongPairTwoSidedCoreMeanWork
open UpperAfter545Remaining

def coreSupport (X s : ℝ) : Finset ℕ := support (distinctSource X s) index
def coreCoefficient (X s : ℝ) (m : ℕ) : ℝ :=
  (coefficient (distinctSource X s) index (originalWeight X s true) m).re

theorem coreRemainder_eq_collected (X s L R : ℝ) :
    distinctRemainder X s L R=
      HarmanDivisorWindow.remainder (coreSupport X s) (coreCoefficient X s) L R := by
  have hh := congrArg Complex.re (grouped_sum (distinctSource X s) index
    (originalWeight X s true) (fun m => (floorKernel L R m:ℂ)))
  rw [HarmanDivisorWindow.remainder_eq_sum]
  simpa only [distinctRemainder,coreSupport,coreCoefficient,floorKernel,
    Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] using hh.symm

theorem support_geometry (X s : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hlog : 1000≤Real.log X) (m : ℕ) (hm : m∈coreSupport X s) :
    X^(26/35:ℝ)<(m:ℝ) ∧ (m:ℝ)<X^((771/1000:ℝ)*(1-3*s)) := by
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hm
  exact LongPairTwoSidedCoreWork.support_geometry X s hX hs hs1 hlog _
    (Finset.mem_image.mpr ⟨r,(Finset.mem_filter.mp hr).1,rfl⟩)

theorem negativeMean_eq_collected (X s Y : ℝ) :
    RestDistinctCoreReductionWork.distinctCoreNegativeMean X s Y=
      (1/X)*(∫ x in Icc X (2*X),max (-HarmanDivisorWindow.remainder
        (coreSupport X s) (coreCoefficient X s) (x-x*(Y/X)) x) 0) := by
  simp only [RestDistinctCoreReductionWork.distinctCoreNegativeMean,coreRemainder_eq_collected]

theorem eventually_coreCoefficient_cap (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ X : ℝ in atTop,1≤X ∧ ∀ (s : ℝ) (m : ℕ),
      0<m → (m:ℝ)≤X^2 → |coreCoefficient X s m|≤X^δ := by
  filter_upwards [LongerTupleEncoding.eventual_coefficient_cap 2 δ hδ] with X hh
  refine ⟨hh.1,?_⟩
  intro s m hm hcap
  have hb := hh.2 (distinctSource X s) (originalWeight X s true)
    (fun r hr => source_length X s r (Finset.mem_filter.mp hr).1)
    (fun r _ => originalWeight_norm_le X s true r) m hm hcap
  exact (Complex.abs_re_le_norm _).trans hb

theorem source_factor_ranges (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) (r : Representation)
    (hr : r∈distinctSource X s) :
    X^(9/35:ℝ)≤(r.1:ℝ) ∧ (r.1:ℝ)<X^(313/1000-3*s:ℝ) ∧
      ∀ q∈r.2.2,q.Prime ∧ X^(229/1000:ℝ)<(q:ℝ) ∧ (q:ℝ)<X^(26/105-s:ℝ) :=
  LongPairTwoSidedCoreWork.source_factor_ranges X s hX hs hs1 hlog r (Finset.mem_filter.mp hr).1

/-- The three large factors really are distinct primes. The distinguished
prime p is larger than either tuple prime; no ordering between a and b
is asserted or needed. -/
theorem source_prime_shape (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) (r : Representation)
    (hr : r∈distinctSource X s) :
    ∃ a b : ℕ,r.2.2=[a,b] ∧ a≠b ∧ a<r.1 ∧ b<r.1 ∧
      r.1.Prime ∧ a.Prime ∧ b.Prime := by
  have hc := (Finset.mem_filter.mp hr).1
  obtain ⟨a,b,he⟩ := List.length_eq_two.mp (source_length X s r hc)
  have hab : a≠b := by simpa [ShortPairSplitWork.prime,he] using (Finset.mem_filter.mp hr).2
  have hf := source_factor_ranges X s hX hs hs1 hlog r hr
  have ha := hf.2.2 a (by simp [he])
  have hb := hf.2.2 b (by simp [he])
  have hpow := Real.rpow_le_rpow_of_exponent_le hX.le
    (by linarith : (26/105:ℝ)-s≤9/35)
  have hap : a<r.1 := by exact_mod_cast (ha.2.2.trans_le hpow).trans_le hf.1
  have hbp : b<r.1 := by exact_mod_cast (hb.2.2.trans_le hpow).trans_le hf.1
  have hcol := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1).1
  have hp := ((LongPairCollectionWork.mem_source X s _ _ r).mp hcol).1
  have hprime := (PositiveSharpSieveDecomposition.large_band_bounds X r.1 hp).1
  exact ⟨a,b,he,hab,hap,hbp,hprime,ha.1,hb.1⟩

#print axioms coreRemainder_eq_collected
#print axioms source_prime_shape
run_cmd do
  for decl in [``coreRemainder_eq_collected, ``support_geometry,
      ``negativeMean_eq_collected, ``eventually_coreCoefficient_cap,
      ``source_factor_ranges, ``source_prime_shape] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end LongPairDistinctCoreWork
