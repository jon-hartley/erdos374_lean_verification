import LongPairHighCoreGeometryWork
import LongPairTwoSidedCoreMeanWork
import RestTwoSidedCoreReductionWork

/-! Exact signed divisor family of the narrowed remaining item-2 core. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace LongPairTwoSidedCoreWork
open LongerTupleEncoding LongerTupleCollection LongerTupleActualProfiles
open LongPairTwoSidedCoreMeanWork LongPairHighCoreGeometryWork
open SieveWeightedCutoffs PositiveSharpBoxedCount UpperAfter545Remaining

def coreSupport (X s : ℝ) : Finset ℕ := support (twoSidedCoreSource X s) index
def coreCoefficient (X s : ℝ) (m : ℕ) : ℝ :=
  (coefficient (twoSidedCoreSource X s) index (originalWeight X s true) m).re

theorem coreRemainder_eq_collected (X s L R : ℝ) :
    twoSidedCoreRemainder X s L R=
      HarmanDivisorWindow.remainder (coreSupport X s) (coreCoefficient X s) L R := by
  have hh := congrArg Complex.re (grouped_sum (twoSidedCoreSource X s) index
    (originalWeight X s true) (fun m => (floorKernel L R m:ℂ)))
  rw [HarmanDivisorWindow.remainder_eq_sum]
  simpa only [twoSidedCoreRemainder,coreSupport,coreCoefficient,floorKernel,
    Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] using hh.symm

theorem support_geometry (X s : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hlog : 1000≤Real.log X) (m : ℕ) (hm : m∈coreSupport X s) :
    X^(26/35:ℝ)<(m:ℝ) ∧ (m:ℝ)<X^((771/1000:ℝ)*(1-3*s)) := by
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hm
  have hcore := (Finset.mem_filter.mp hr).1
  have hhigh := (Finset.mem_filter.mp (Finset.mem_filter.mp hcore).1).2
  exact ⟨hhigh,core_source_upper X s hX hs hs1 hlog r hcore⟩

theorem negativeMean_eq_collected (X s Y : ℝ) :
    RestTwoSidedCoreReductionWork.twoSidedCoreNegativeMean X s Y=
      (1/X)*(∫ x in Icc X (2*X),max (-HarmanDivisorWindow.remainder
        (coreSupport X s) (coreCoefficient X s) (x-x*(Y/X)) x) 0) := by
  simp only [RestTwoSidedCoreReductionWork.twoSidedCoreNegativeMean,coreRemainder_eq_collected]

theorem eventually_coreCoefficient_cap (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ X : ℝ in atTop, 1≤X ∧ ∀ (s : ℝ) (m : ℕ),
      0<m → (m:ℝ)≤X^2 → |coreCoefficient X s m|≤X^δ := by
  filter_upwards [LongerTupleEncoding.eventual_coefficient_cap 2 δ hδ] with X hh
  refine ⟨hh.1,?_⟩
  intro s m hm hcap
  have hb := hh.2 (twoSidedCoreSource X s) (originalWeight X s true)
    (fun r hr => ((LongPairCollectionWork.mem_source X s _ _ r).mp
      (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1).1).2.2.2.1)
    (fun r _ => originalWeight_norm_le X s true r) m hm hcap
  exact (Complex.abs_re_le_norm _).trans hb

/-- Every retained tuple prime, not just a designated position, is
strictly above the new edge cutoff. -/
theorem source_both_primes_gt (X s : ℝ) (r : Representation)
    (hr : r∈twoSidedCoreSource X s) :
    ∀ q∈r.2.2, X^(229/1000:ℝ)<(q:ℝ) := by
  have hfirst := (Finset.mem_filter.mp hr).2
  have hsecond := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2
  have hc := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1).1
  have hlen := ((LongPairCollectionWork.mem_source X s _ _ r).mp hc).2.2.2.1
  obtain ⟨a,b,he⟩ := List.length_eq_two.mp hlen
  have ha : X^(229/1000:ℝ)<(a:ℝ) := by
    simpa [ShortPairSplitWork.prime,he] using hfirst
  have hb : X^(229/1000:ℝ)<(b:ℝ) := by
    simpa [ShortPairSplitWork.prime,he] using hsecond
  intro q hq
  rw [he] at hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl
  · exact ha
  · exact hb

/-- Exact prime length ranges for future structure-preserving estimates:
the distinguished large prime is in [.257142..., .313-3s), and both
tuple primes are in (.229, .247619...-s). -/
theorem source_factor_ranges (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) (r : Representation)
    (hr : r∈twoSidedCoreSource X s) :
    X^(9/35:ℝ)≤(r.1:ℝ) ∧ (r.1:ℝ)<X^(313/1000-3*s:ℝ) ∧
      ∀ q∈r.2.2, q.Prime ∧ X^(229/1000:ℝ)<(q:ℝ) ∧
        (q:ℝ)<X^(26/105-s:ℝ) := by
  have hc := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1).1
  obtain ⟨hp,_,ht,hlen,_,_⟩ := (LongPairCollectionWork.mem_source X s _ _ r).mp hc
  have hband := PositiveSharpSieveDecomposition.large_band_bounds X r.1 hp
  have hX0 : 0<X := by linarith
  have hp0 : (0:ℝ)<r.1 := by exact_mod_cast hband.1.pos
  have hg := large_band_geometry X s hX hs hs1 hlog r.1 hp
  have hpool := (LongerTupleGeometry.family_data _ s _ hg.2.2.1 hs r.2.2 (Or.inl ht)).1
  have hpLog := Real.log_le_log (Real.rpow_pos_of_pos hX0 _) hband.2.1
  rw [Real.log_rpow hX0] at hpLog
  have bounds (q : ℕ) (hq : q∈r.2.2) :
      q.Prime ∧ X^(229/1000:ℝ)<(q:ℝ) ∧
        Real.log (q:ℝ)<((1-3*s)*Real.log X-Real.log (r.1:ℝ))/3 := by
    have hh := (SieveBoxedFamily.mem_pool _ s _ q).mp (hpool q hq)
    have hq0 : (0:ℝ)<q := by exact_mod_cast hh.1.pos
    have hlt := Real.log_lt_log hq0 hh.2.1
    rw [SieveWeightedCutoffs.log_three X s r.1 hX0 hp0] at hlt
    exact ⟨hh.1,source_both_primes_gt X s r hr q hq,hlt⟩
  let q := ShortPairSplitWork.prime true r
  have hq := ShortPairSplitWork.prime_mem true r hlen
  have hb := bounds q hq
  have hqLog := Real.log_lt_log (Real.rpow_pos_of_pos hX0 _) hb.2.1
  rw [Real.log_rpow hX0] at hqLog
  have hupperLog : Real.log (r.1:ℝ)<(313/1000-3*s)*Real.log X := by
    linarith [hb.2.2]
  refine ⟨hband.2.1,?_,?_⟩
  · apply (Real.log_lt_log_iff hp0 (Real.rpow_pos_of_pos hX0 _)).mp
    simpa only [Real.log_rpow hX0] using hupperLog
  · intro n hn
    have hb := bounds n hn
    have hn0 : (0:ℝ)<n := by exact_mod_cast hb.1.pos
    refine ⟨hb.1,hb.2.1,?_⟩
    apply (Real.log_lt_log_iff hn0 (Real.rpow_pos_of_pos hX0 _)).mp
    rw [Real.log_rpow hX0]
    linarith [hb.2.2]

#print axioms coreRemainder_eq_collected
#print axioms support_geometry
#print axioms source_factor_ranges
run_cmd do
  for decl in [``coreRemainder_eq_collected, ``support_geometry,
      ``negativeMean_eq_collected, ``eventually_coreCoefficient_cap,
      ``source_both_primes_gt, ``source_factor_ranges] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end LongPairTwoSidedCoreWork

