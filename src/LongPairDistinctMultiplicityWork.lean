import LargePrimeRepresentationWork

/-! Constant, phase-uniform collision bounds for the exact distinct-prime
core. The small divisor is below every large prime and the distinguished
prime is above both tuple-prime ranges, including across representations. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LongPairDistinctMultiplicityWork
open LongerTupleEncoding LongerTupleCollection LongerTupleActualProfiles
open LongPairDistinctCoreWork LongPairRepeatedCoreMeanWork
open LongPairTwoSidedCoreMeanWork SieveWeightedCutoffs PositiveSharpBoxedCount
open LargePrimeRepresentationWork

def swap (r : Representation) : Representation := (r.1,r.2.1,r.2.2.reverse)

theorem source_small_divisor_power (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) (r : Representation)
    (hr : r∈distinctSource X s) : 0<r.2.1 ∧ (r.2.1:ℝ)<X^s := by
  have hc := (Finset.mem_filter.mp hr).1
  have hcol := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1).1
  obtain ⟨hp,hd,_,_,_,_⟩ := (LongPairCollectionWork.mem_source X s _ _ r).mp hcol
  have hg := large_band_geometry X s hX hs hs1 hlog r.1 hp
  have hX0 : 0<X := by linarith
  have hp1 : (1:ℝ)≤r.1 := by exact_mod_cast (by omega : 1≤r.1)
  have hlvl : 0≤level X s := by unfold level; exact Real.rpow_nonneg hX0.le _
  have hDle : level X s/(r.1:ℝ)≤X := by
    apply (div_le_self hlvl hp1).trans
    unfold level
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX.le
      (by linarith : 1-3*s≤(1:ℝ))
  have hdlt := PositiveSharpRemainderSupportGeometry.smallCarrier_lt _ s hg.2.2.1 hs
    (by linarith) r.2.1 hd
  have hpow := Real.rpow_le_rpow (by linarith [hg.2.2.1] : 0≤level X s/(r.1:ℝ)) hDle hs.le
  exact ⟨UpperAfter545Geometry.smallCarrier_pos _ _ _ hd,hdlt.trans_le hpow⟩

theorem source_small_divisor (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) (r : Representation)
    (hr : r∈distinctSource X s) : 0<r.2.1 ∧ (r.2.1:ℝ)<X^(1/100:ℝ) := by
  have hd := source_small_divisor_power X s hX hs hs1 hlog r hr
  exact ⟨hd.1,hd.2.trans_le (Real.rpow_le_rpow_of_exponent_le hX.le
    (by linarith : s≤(1/100:ℝ)))⟩

theorem cross_prime_lt (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) (r t : Representation)
    (hr : r∈distinctSource X s) (ht : t∈distinctSource X s)
    (q : ℕ) (hq : q∈t.2.2) : q<r.1 := by
  have hR := source_factor_ranges X s hX hs hs1 hlog r hr
  have hT := source_factor_ranges X s hX hs hs1 hlog t ht
  have hpow := Real.rpow_le_rpow_of_exponent_le hX.le
    (by linarith : (26/105:ℝ)-s≤9/35)
  exact_mod_cast ((hT.2.2 q hq).2.2.trans_le hpow).trans_le hR.1

theorem cross_small_lt_prime (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) (r t : Representation)
    (hr : r∈distinctSource X s) (ht : t∈distinctSource X s)
    (q : ℕ) (hq : q∈r.2.2) : t.2.1<q := by
  have hd := (source_small_divisor X s hX hs hs1 hlog t ht).2
  have hqlo := (source_factor_ranges X s hX hs hs1 hlog r hr).2.2 q hq
  have hpow := Real.rpow_le_rpow_of_exponent_le hX.le
    (by norm_num : (1/100:ℝ)≤229/1000)
  exact_mod_cast (hd.trans_le hpow).trans hqlo.2.1

/-- All full-modulus collisions are precisely equality or a tuple swap.
The swap need not itself belong to the source. -/
theorem source_collision (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) (r t : Representation)
    (hr : r∈distinctSource X s) (ht : t∈distinctSource X s)
    (he : index r=index t) : r=t ∨ r=swap t := by
  obtain ⟨a,b,hR,hab,_,_,hp,ha,hb⟩ := source_prime_shape X s hX hs hs1 hlog r hr
  obtain ⟨a',b',hT,_,_,_,hp',ha',hb'⟩ := source_prime_shape X s hX hs hs1 hlog t ht
  have hd := source_small_divisor X s hX hs hs1 hlog t ht
  have hpLow := (source_factor_ranges X s hX hs hs1 hlog r hr).1
  have hpow := Real.rpow_le_rpow_of_exponent_le hX.le
    (by norm_num : (1/100:ℝ)≤9/35)
  have hdp : t.2.1<r.1 := by exact_mod_cast (hd.2.trans_le hpow).trans_le hpLow
  have hap := cross_prime_lt X s hX hs hs1 hlog r t hr ht a' (by simp [hT])
  have hbp := cross_prime_lt X s hX hs hs1 hlog r t hr ht b' (by simp [hT])
  have hda := cross_small_lt_prime X s hX hs hs1 hlog r t hr ht a (by simp [hR])
  have hdb := cross_small_lt_prime X s hX hs hs1 hlog r t hr ht b (by simp [hR])
  have he' : r.1*r.2.1*a*b=t.1*t.2.1*a'*b' := by
    simpa [index,hR,hT,Nat.mul_assoc] using he
  obtain ⟨hP,hD,hpair⟩ := triple_rigidity r.1 r.2.1 a b t.1 t.2.1 a' b'
    hp ha hb hp' ha' hb' hd.1 hdp hap hbp hda hdb hab he'
  rcases hpair with ⟨hA,hB⟩ | ⟨hA,hB⟩
  · apply Or.inl
    apply Prod.ext hP
    apply Prod.ext hD
    rw [hR,hT,hA,hB]
  · apply Or.inr
    apply Prod.ext
    · exact hP
    apply Prod.ext
    · exact hD
    simp [swap,hR,hT,hA,hB]

theorem fiber_card_le_two (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X)
    (S : Finset Representation) (hS : S⊆distinctSource X s) (m : ℕ) :
    (S.filter (fun r => index r=m)).card≤2 := by
  let F := S.filter (fun r => index r=m)
  by_cases hn : F.Nonempty
  · obtain ⟨t,ht⟩ := hn
    have hsub : F⊆{t,swap t} := by
      intro r hr
      have hR := Finset.mem_filter.mp hr
      have hT := Finset.mem_filter.mp ht
      have he := source_collision X s hX hs hs1 hlog r t (hS hR.1) (hS hT.1)
        (hR.2.trans hT.2.symm)
      simpa only [Finset.mem_insert,Finset.mem_singleton] using he
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · have he := Finset.not_nonempty_iff_eq_empty.mp hn
    change F.card≤2
    rw [he,Finset.card_empty]
    omega

/-- Uniform for arbitrary unit complex weights, including mask phases.
No ambient positive-power coefficient loss remains. -/
theorem coefficient_norm_le_two (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X)
    (S : Finset Representation) (hS : S⊆distinctSource X s)
    (w : Representation→ℂ) (hw : ∀ r∈S,‖w r‖≤1) (m : ℕ) :
    ‖coefficient S index w m‖≤2 := by
  calc
    _ ≤ ∑ r∈S.filter (fun r => index r=m),‖w r‖ := norm_sum_le _ _
    _ ≤ ∑ _r∈S.filter (fun r => index r=m),(1:ℝ) :=
      Finset.sum_le_sum (fun r hr => hw r (Finset.mem_filter.mp hr).1)
    _ = ((S.filter (fun r => index r=m)).card:ℝ) := by simp
    _ ≤ 2 := by exact_mod_cast fiber_card_le_two X s hX hs hs1 hlog S hS m

theorem coreCoefficient_abs_le_two (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) (m : ℕ) :
    |coreCoefficient X s m|≤2 := by
  exact (Complex.abs_re_le_norm _).trans
    (coefficient_norm_le_two X s hX hs hs1 hlog (distinctSource X s)
      (by intro r hr; exact hr) (originalWeight X s true)
      (fun r _ => originalWeight_norm_le X s true r) m)

#print axioms source_collision
#print axioms coreCoefficient_abs_le_two
run_cmd do
  for decl in [``source_small_divisor_power, ``source_small_divisor, ``cross_prime_lt, ``cross_small_lt_prime,
      ``source_collision, ``fiber_card_le_two, ``coefficient_norm_le_two,
      ``coreCoefficient_abs_le_two] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end LongPairDistinctMultiplicityWork
