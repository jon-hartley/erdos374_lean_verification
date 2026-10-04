import RestSeparatedCoreReductionWork

/-! Literal signed collection of the farther-apart distinct-prime core,
with uniform coefficient bound two and all original source geometry. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace LongPairSeparatedCoreWork
open LongerTupleEncoding LongerTupleCollection LongerTupleActualProfiles
open LongPairCloseDistinctMeanWork LongPairDistinctCoreWork LongPairDistinctMultiplicityWork
open RestSeparatedCoreReductionWork UpperAfter545Remaining

def coreSupport (X s : ℝ) : Finset ℕ := support (separatedSource X s) LongerTupleEncoding.index
def coreCoefficient (X s : ℝ) (m : ℕ) : ℝ :=
  (coefficient (separatedSource X s) LongerTupleEncoding.index (originalWeight X s true) m).re

theorem coreRemainder_eq_collected (X s L R : ℝ) :
    separatedRemainder X s L R=
      HarmanDivisorWindow.remainder (coreSupport X s) (coreCoefficient X s) L R := by
  have hh := congrArg Complex.re (grouped_sum (separatedSource X s) LongerTupleEncoding.index
    (originalWeight X s true) (fun m => (floorKernel L R m:ℂ)))
  rw [HarmanDivisorWindow.remainder_eq_sum]
  simpa only [separatedRemainder,coreSupport,coreCoefficient,floorKernel,
    Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] using hh.symm

theorem support_geometry (X s : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hlog : 1000≤Real.log X) (m : ℕ) (hm : m∈coreSupport X s) :
    X^(26/35:ℝ)<(m:ℝ) ∧ (m:ℝ)<X^((771/1000:ℝ)*(1-3*s)) := by
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hm
  exact LongPairDistinctCoreWork.support_geometry X s hX hs hs1 hlog _
    (Finset.mem_image.mpr ⟨r,(Finset.mem_filter.mp hr).1,rfl⟩)

theorem negativeMean_eq_collected (X s Y : ℝ) :
    separatedCoreNegativeMean X s Y=
      (1/X)*(∫ x in Icc X (2*X),max (-HarmanDivisorWindow.remainder
        (coreSupport X s) (coreCoefficient X s) (x-x*(Y/X)) x) 0) := by
  simp only [separatedCoreNegativeMean,coreRemainder_eq_collected]

theorem coreCoefficient_abs_le_two (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) (m : ℕ) :
    |coreCoefficient X s m|≤2 :=
  (Complex.abs_re_le_norm _).trans
    (coefficient_norm_le_two X s hX hs hs1 hlog (separatedSource X s)
      (fun _ hr => (Finset.mem_filter.mp hr).1) (originalWeight X s true)
      (fun r _ => originalWeight_norm_le X s true r) m)

theorem source_prime_shape (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) (r : Representation)
    (hr : r∈separatedSource X s) :
    ∃ a b : ℕ,r.2.2=[a,b] ∧ a≠b ∧ a<r.1 ∧ b<r.1 ∧
      r.1.Prime ∧ a.Prime ∧ b.Prime ∧ X^(9/50:ℝ)<(Nat.dist a b:ℝ) := by
  obtain ⟨hr,hgap⟩ := Finset.mem_filter.mp hr
  obtain ⟨a,b,he,hab,hap,hbp,hp,ha,hb⟩ :=
    LongPairDistinctCoreWork.source_prime_shape X s hX hs hs1 hlog r hr
  exact ⟨a,b,he,hab,hap,hbp,hp,ha,hb,by simpa [tupleGap,ShortPairSplitWork.prime,he] using hgap⟩

theorem source_factor_ranges (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) (r : Representation)
    (hr : r∈separatedSource X s) :
    X^(9/35:ℝ)≤(r.1:ℝ) ∧ (r.1:ℝ)<X^(313/1000-3*s:ℝ) ∧
      ∀ q∈r.2.2,q.Prime ∧ X^(229/1000:ℝ)<(q:ℝ) ∧ (q:ℝ)<X^(26/105-s:ℝ) :=
  LongPairDistinctCoreWork.source_factor_ranges X s hX hs hs1 hlog r (Finset.mem_filter.mp hr).1

#print axioms coreRemainder_eq_collected
#print axioms coreCoefficient_abs_le_two
#print axioms source_prime_shape
run_cmd do
  for decl in [``coreRemainder_eq_collected, ``support_geometry,
      ``negativeMean_eq_collected, ``coreCoefficient_abs_le_two,
      ``source_prime_shape, ``source_factor_ranges] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end LongPairSeparatedCoreWork
