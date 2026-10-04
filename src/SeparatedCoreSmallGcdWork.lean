import SeparatedCoreShiftSpacingWork

/-! For nearby distinct products, the gcd of their source indices is
exactly the gcd of the original small sieve divisors. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Set
attribute [local instance] Classical.propDecidable
namespace SeparatedCoreSmallGcdWork
open LongerTupleEncoding LongPairCloseDistinctMeanWork LongPairSeparatedCoreWork
open SeparatedCoreSharedPrimeWork PositiveSharpPowerWindow
open SieveWeightedCutoffs PositiveSharpBoxedCount UpperAfter545Remaining

theorem source_small_divisor (X s : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hlog : 1000≤Real.log X) (r : Representation) (hr : r∈separatedSource X s) :
    0<r.2.1 ∧ (r.2.1:ℝ)≤X^s := by
  have hc := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
  have hcol := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1).1
  obtain ⟨hp,hd,_,_,_,_⟩ := (LongPairCollectionWork.mem_source X s _ _ r).mp hcol
  have hg := LongerTupleActualProfiles.large_band_geometry X s hX hs hs1 hlog r.1 hp
  have hXp : 0<X := by linarith
  have hp1 : (1:ℝ)≤r.1 := by exact_mod_cast (by omega : 1≤r.1)
  have hlvl : 0≤level X s := by unfold level; exact Real.rpow_nonneg hXp.le _
  have hDle : level X s/(r.1:ℝ)≤X := by
    apply (div_le_self hlvl hp1).trans
    unfold level
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX.le
      (by linarith : 1-3*s≤(1:ℝ))
  have hdle := (PositiveSharpRemainderSupportGeometry.smallCarrier_lt _ s hg.2.2.1 hs
    (by linarith) r.2.1 hd).le.trans
    (Real.rpow_le_rpow (by linarith [hg.2.2.1] : 0≤level X s/(r.1:ℝ)) hDle hs.le)
  refine ⟨?_,hdle⟩
  have hi := (support_geometry X s hX hs hs1 hlog (index r)
    (Finset.mem_image.mpr ⟨r,hr,rfl⟩)).1
  have hip : (0:ℝ)<(index r:ℝ) := (Real.rpow_pos_of_pos hXp _).trans hi
  by_contra hh
  have hz : r.2.1=0 := by omega
  simp [index,hz] at hip

theorem largeFactor_prime (X s : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hlog : 1000≤Real.log X) (r : Representation) (hr : r∈separatedSource X s)
    (q : ℕ) (hq : q∈largeFactors r) : q.Prime := by
  rcases List.mem_cons.mp hq with he | hq
  · subst q
    obtain ⟨a,b,_,_,_,_,hp,_⟩ := source_prime_shape X s hX hs hs1 hlog r hr
    exact hp
  · exact (source_factor_ranges X s hX hs hs1 hlog r hr).2.2 q hq |>.1

theorem prime_coprime_list (q : ℕ) (l : List ℕ) (hq : q.Prime)
    (hl : ∀p∈l,p.Prime) (hne : q∉l) : Nat.Coprime q l.prod := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.prod_cons,Nat.coprime_mul_iff_right]
    refine ⟨?_,ih (fun t ht => hl t (by simp [ht])) (fun ht => hne (by simp [ht]))⟩
    apply hq.coprime_iff_not_dvd.mpr
    intro hd
    have he : q=p := ((hl p (by simp)).eq_one_or_self_of_dvd q hd).resolve_left hq.ne_one
    exact hne (by simp [he])

theorem list_coprime_of_each (l : List ℕ) (d : ℕ)
    (h : ∀q∈l,Nat.Coprime q d) : Nat.Coprime l.prod d := by
  induction l with
  | nil => simp
  | cons p l ih =>
    exact Nat.coprime_mul_iff_left.mpr
      ⟨h p (by simp),ih (fun q hq => h q (by simp [hq]))⟩

theorem largeFactors_coprime_small (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X)
    (r r' : Representation) (hr : r∈separatedSource X s) (hr' : r'∈separatedSource X s) :
    Nat.Coprime (largeFactors r).prod r'.2.1 := by
  apply list_coprime_of_each
  intro q hq
  apply (largeFactor_prime X s hX hs hs1 hlog r hr q hq).coprime_iff_not_dvd.mpr
  intro hd
  have hsmall := source_small_divisor X s hX hs hs1 hlog r' hr'
  have hle : (q:ℝ)≤r'.2.1 := by exact_mod_cast Nat.le_of_dvd hsmall.1 hd
  have hlow := largeFactor_lower X s hX hs hs1 hlog r hr q hq
  have hpow := Real.rpow_lt_rpow_of_exponent_lt hX (by linarith : s<(229/1000:ℝ))
  linarith

theorem index_eq_large_mul_small (r : Representation) :
    index r=(largeFactors r).prod*r.2.1 := by
  simp only [index,largeFactors,List.prod_cons]
  ring

theorem gcd_eq_small_of_disjoint (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X)
    (r r' : Representation) (hr : r∈separatedSource X s) (hr' : r'∈separatedSource X s)
    (hdis : disjointLarge r r') : Nat.gcd (index r) (index r')=Nat.gcd r.2.1 r'.2.1 := by
  have hlarge : Nat.Coprime (largeFactors r).prod (largeFactors r').prod := by
    apply list_coprime_of_each
    intro q hq
    exact prime_coprime_list q _ (largeFactor_prime X s hX hs hs1 hlog r hr q hq)
      (largeFactor_prime X s hX hs hs1 hlog r' hr') (hdis q hq)
  have hc := Nat.coprime_mul_iff_right.mpr
    ⟨hlarge,largeFactors_coprime_small X s hX hs hs1 hlog r r' hr hr'⟩
  rw [index_eq_large_mul_small r,index_eq_large_mul_small r',hc.gcd_mul_left_cancel]
  exact (largeFactors_coprime_small X s hX hs hs1 hlog r' r hr' hr).gcd_mul_left_cancel_right _

theorem nearby_gcd_eq_small (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X)
    (n m : ℕ) (hne : n≠m) (hgap : |(n:ℝ)-m|<2*halfWidth X (101/1000))
    (r r' : Representation) (hr : r∈separatedSource X s) (hr' : r'∈separatedSource X s)
    (hn : index r∣n) (hm : index r'∣m) :
    Nat.gcd (index r) (index r')=Nat.gcd r.2.1 r'.2.1 :=
  gcd_eq_small_of_disjoint X s hX hs hs1 hlog r r' hr hr'
    (nearby_representations_disjoint X s hX hs hs1 hlog n m hne hgap r r' hr hr' hn hm)

theorem disjoint_lcm_lower (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X)
    (r r' : Representation) (hr : r∈separatedSource X s) (hr' : r'∈separatedSource X s)
    (hdis : disjointLarge r r') :
    X^(52/35-s:ℝ)<(Nat.lcm (index r) (index r'):ℝ) := by
  have hXp : 0<X := by linarith
  have hd := source_small_divisor X s hX hs hs1 hlog r hr
  have hg : (Nat.gcd (index r) (index r'):ℝ)≤X^s := by
    rw [gcd_eq_small_of_disjoint X s hX hs hs1 hlog r r' hr hr' hdis]
    exact (show (Nat.gcd r.2.1 r'.2.1:ℝ)≤r.2.1 by
      exact_mod_cast Nat.gcd_le_left r'.2.1 hd.1).trans hd.2
  have ha := (support_geometry X s hX hs hs1 hlog (index r)
    (Finset.mem_image.mpr ⟨r,hr,rfl⟩)).1
  have hb := (support_geometry X s hX hs hs1 hlog (index r')
    (Finset.mem_image.mpr ⟨r',hr',rfl⟩)).1
  have hprod := mul_lt_mul ha hb.le (Real.rpow_pos_of_pos hXp (26/35:ℝ))
    (Nat.cast_nonneg (index r) : (0:ℝ)≤(index r:ℝ))
  rw [← Real.rpow_add hXp] at hprod
  norm_num at hprod
  have hid : (Nat.gcd (index r) (index r'):ℝ)*(Nat.lcm (index r) (index r'):ℝ)=
      (index r:ℝ)*(index r':ℝ) := by exact_mod_cast Nat.gcd_mul_lcm (index r) (index r')
  have hh := hprod.trans_le (hid.symm.le.trans
    (mul_le_mul_of_nonneg_right hg (Nat.cast_nonneg _)))
  have he : X^(52/35:ℝ)=X^s*X^(52/35-s:ℝ) := by
    rw [← Real.rpow_add hXp]
    congr 1
    ring
  rw [he] at hh
  have hpos := Real.rpow_pos_of_pos hXp s
  nlinarith

run_cmd do
  for decl in [``source_small_divisor, ``largeFactor_prime, ``prime_coprime_list,
      ``list_coprime_of_each, ``largeFactors_coprime_small, ``index_eq_large_mul_small,
      ``gcd_eq_small_of_disjoint, ``nearby_gcd_eq_small, ``disjoint_lcm_lower] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end SeparatedCoreSmallGcdWork
