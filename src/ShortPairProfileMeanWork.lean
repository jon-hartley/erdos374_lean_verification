import ShortPairProfilesWork

/-! Literal short-pair profile second means, with actual-completion activity. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ShortPairProfileMeanWork
open ShortPairProfilesWork ShortPairSplitWork LongerTupleActualProfiles
open LongerTupleEncoding (Representation)
open LongerTupleProfile SieveWeightedCutoffs SieveBoxedFamily SieveGeometricGrid
open ShortSingletonMasks ShortSingletonEndpoints UpperAfter545Remaining

def completionRelation (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (m q : ℕ) : Prop :=
  ∃ a ∈ pairSupport X s P z second js,
    ShortPairSplitWork.index a=m ∧ rebuild second a q ∈ pairSource X s P z second js

theorem source_physical (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (hjs : js.length=2) (hX : 1<X)
    (hs : 0<s) (hs1 : s≤1/1000) (hg : BandGeometry X s P z) (r : Representation)
    (hr : r∈pairSource X s P z second js) :
    (LongerTupleEncoding.index r:ℝ)<X^(1-3*s/2) := by
  obtain ⟨hp,hd,ht,_,_⟩ := (mem_source X s P z true js r).mp (Finset.mem_filter.mp hr).1
  have hlen := pairSource_length X s P z second js hjs r hr
  exact LongerTupleGeometry.physical_product_lt X s (z r.1) r.1 r.2.1 r.2.2 hX hs hs1
    (by have hh := (hg r.1 hp).1; omega) (hg r.1 hp).2.2.1 (hg r.1 hp).2.2.2 hd
    (by intro he; simp only [he,List.length_nil] at hlen; omega)
    (family_mem_or true _ s _ r.2.2 ht)

theorem source_prime_lower (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (hjs : js.length=2) (hX : 1<X)
    (hs : 0<s) (hs1 : s≤1/1000) (hlog : 1000≤Real.log X)
    (hg : BandGeometry X s P z) (r : Representation)
    (hr : r∈pairSource X s P z second js) :
    X^((49/100:ℝ)*s^2)≤(prime second r:ℝ) := by
  have hsource := (Finset.mem_filter.mp hr).1
  have hp := (mem_source X s P z true js r).mp hsource |>.1
  have hgeom := hg r.1 hp
  have hm := source_matches X s P z true js hs hg r hsource
  have hpool := matches_pool _ s _ hgeom.2.2.1 hs r.2.2 js hm
    (prime second r) (prime_mem second r (pairSource_length X s P z second js hjs r hr))
  have hq := (mem_pool _ s _ _).mp hpool
  have hXp : 0<X := by linarith
  have hpp : (0:ℝ)<r.1 := by
    exact_mod_cast (by have hh := hgeom.1; omega : 0<r.1)
  have hpcap := hgeom.2.1.trans (ShortSingletonGeometry.sqrt_two_mul_le X hX hlog)
  have hDlo : X^(49/100:ℝ)≤level X s/r.1 := by
    apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hXp _) (by linarith : 0<level X s/r.1)).mp
    rw [Real.log_rpow hXp,level,Real.log_div (Real.rpow_pos_of_pos hXp _).ne' hpp.ne',
      Real.log_rpow hXp]
    have hpLog := Real.log_le_log hpp hpcap
    rw [Real.log_rpow hXp] at hpLog
    have hsLog := mul_le_mul_of_nonneg_right hs1 (Real.log_pos hX).le
    nlinarith
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hXp.le _) hDlo (sq_nonneg s)
  rw [←Real.rpow_mul hXp.le] at hh
  exact hh.trans hq.2.2

theorem support_bounds (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (hjs : js.length=2) (hX : 1<X)
    (hs : 0<s) (hs1 : s≤1/1000) (hg : BandGeometry X s P z) (a : PairRep)
    (ha : a∈pairSupport X s P z second js) :
    2≤ShortPairSplitWork.index a ∧ (ShortPairSplitWork.index a:ℝ)≤X := by
  have hpos := pairSupport_index_pos X s P z second js hjs (by linarith) a ha
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ha
  have hp := (mem_source X s P z true js r).mp (Finset.mem_filter.mp hr).1 |>.1
  have hdiv : r.1 ∣ ShortPairSplitWork.index (drop second r) := by
    simpa only [ShortPairSplitWork.index,drop,Nat.mul_assoc] using
      dvd_mul_right r.1 (r.2.1 * r.2.2.getD (if second then 0 else 1) 1)
  have hqp : 0<prime second r := by
    have hh := pairSource_prime_mem X s P z second js hjs (by linarith) hs hg r hr
    exact ((mem_primeSupport X _ (by linarith)).mp hh).1.pos
  have hle : ShortPairSplitWork.index (drop second r)≤LongerTupleEncoding.index r := by
    rw [index_drop second r (pairSource_length X s P z second js hjs r hr)]
    exact Nat.le_mul_of_pos_right _ hqp
  refine ⟨(hg r.1 hp).1.trans (Nat.le_of_dvd hpos hdiv),?_⟩
  have htop : X^(1-3*s/2)≤X := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX.le
      (show 1-3*s/2≤(1:ℝ) by linarith)
  exact (show (ShortPairSplitWork.index (drop second r):ℝ)≤(LongerTupleEncoding.index r:ℝ)
    by exact_mod_cast hle).trans ((source_physical X s P z second js hjs hX hs hs1 hg r hr).le.trans htop)

theorem relation_bounds (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (hjs : js.length=2) (hX : 1<X)
    (hs : 0<s) (hs1 : s≤1/1000) (hlog : 1000≤Real.log X)
    (hg : BandGeometry X s P z) (m q : ℕ)
    (hr : completionRelation X s P z second js m q) :
    X^(109/200:ℝ)<(m:ℝ)*(q:ℝ) ∧ (m:ℝ)*(q:ℝ)<X^(1-3*s/2) ∧
      X^((49/100:ℝ)*s^2)≤(q:ℝ) ∧ (q:ℝ)≤X^(8/35:ℝ) := by
  obtain ⟨a,ha,he,hc⟩ := hr
  have hh := (mem_source X s P z true js _).mp (Finset.mem_filter.mp hc).1 |>.2.2.2.2
  have hphys := source_physical X s P z second js hjs hX hs hs1 hg _ hc
  have hlo := source_prime_lower X s P z second js hjs hX hs hs1 hlog hg _ hc
  have hshort := (Finset.mem_filter.mp hc).2.1
  rw [prime_rebuild] at hlo hshort
  rw [ShortPairSplitWork.index_rebuild,he,Nat.cast_mul] at hh hphys
  exact ⟨hh,hphys,hlo,hshort⟩

theorem mask_zero (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (hjs : js.length=2) (hX : 1<X)
    (hs : 0<s) (hg : BandGeometry X s P z) (a : PairRep)
    (ha : a∈pairSupport X s P z second js) (q : ℕ) (hq : q∈primeSupport X)
    (hn : ¬completionRelation X s P z second js (ShortPairSplitWork.index a) q) :
    (prefixIndicator (pairHi X s z second js a) q-prefixIndicator (pairLo X s second js a) q)*
      (1-prefixIndicator (physicalCut X (ShortPairSplitWork.index a)) q)=0 := by
  have hc := ShortPairProfilesWork.completion_iff X s P z second js hjs (by linarith) hs hg a ha q hq
  have hp : a.1∈P := by
    obtain ⟨r,hr,he⟩ := Finset.mem_image.mp ha
    rw [←he]
    exact ((mem_source X s P z true js r).mp (Finset.mem_filter.mp hr).1).1
  have hgeom := hg a.1 hp
  have he := box_pool_high_prefix X (level X s/a.1) s (z a.1) (selectedIndex second js)
    (ShortPairSplitWork.index a) q (by linarith) (by linarith [hgeom.2.2.1])
    (pairSupport_cutoff_pos X s P z second js hjs hs hg a ha)
    (pairSupport_index_pos X s P z second js hjs (by linarith) a ha)
  have hncond := fun hb => hn ⟨a,ha,rfl,hc.mpr hb⟩
  simpa only [pairHi,pairLo,ite_eq_right hncond] using he.symm

theorem eventually_pair_square (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ X : ℝ in atTop, 1<X ∧ 1000≤Real.log X ∧
      ∀ (P : Finset ℕ) (z : ℝ → ℝ) (second : Bool) (js : List ℕ),
        js.length=2 → BandGeometry X s P z →
        let Y : ℝ := X^(101/1000:ℝ)/2
        (1/X)*(∫ x in Icc X (2*X), pairKernel X s P z second js
          (floorKernel (x-x*(Y/X)) x)^2)≤Y^2*X^(-c) := by
  obtain ⟨c,hc,hmean⟩ := LongerTupleGlobalMean.eventually_bound (α:=PairRep) s hs hs1 3
  refine ⟨c,hc,?_⟩
  filter_upwards [hmean,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1000)] with X hm hX hlog
  refine ⟨hX,hlog,?_⟩
  intro P z second js hjs hg
  dsimp only
  have hb := hm.2 (pairSupport X s P z second js) ShortPairSplitWork.index ShortPairSplitWork.encode
    (primeSupport X) (completionRelation X s P z second js) (primeCutoff X) (pairWeight X s)
    (pairLo X s second js) (pairHi X s z second js) (physicalCut X)
    (fun a _ => ShortPairSplitWork.encode_product a)
    (fun a _ b _ he => ShortPairSplitWork.encode_injective he)
    (by intro m hm; obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hm
        exact support_bounds X s P z second js hjs hX hs hs1 hg a ha)
    (fun q hq => ⟨(primeSupport_bounds X hX.le q hq).1,(primeSupport_bounds X hX.le q hq).2.1⟩)
    (fun q hq => (primeSupport_bounds X hX.le q hq).2.2) (primeCutoff_le X hX.le)
    (by intro a _; rw [pairWeight,Complex.norm_real,Real.norm_eq_abs]
        exact SieveSmallWeights.weight_abs_le_one _ _ true a.2.1)
    (fun m _ q _ hr => relation_bounds X s P z second js hjs hX hs hs1 hlog hg m q hr)
    (fun a ha q hq hn => mask_zero X s P z second js hjs hX hs hg a ha q hq hn)
  have heq : (fun x : ℝ => pairKernel X s P z second js
      (floorKernel (x-x*((X^(101/1000:ℝ)/2)/X)) x)^2) =
      (fun x => (pairMaskedSum X s P z second js (x-x*((X^(101/1000:ℝ)/2)/X)) x).re^2) := by
    funext x
    have he := congrArg Complex.re (pairKernel_eq_masked X s P z second js hjs hX hs hg
      (x-x*((X^(101/1000:ℝ)/2)/X)) x)
    simpa only [Complex.ofReal_re] using congrArg (fun r:ℝ => r^2) he
  rw [heq]
  exact hb

#print axioms eventually_pair_square
run_cmd do
  for decl in [``source_physical, ``source_prime_lower, ``support_bounds,
      ``relation_bounds, ``mask_zero, ``eventually_pair_square] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end ShortPairProfileMeanWork
