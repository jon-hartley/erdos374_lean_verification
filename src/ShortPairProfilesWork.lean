import ShortPairSplitWork

/-! Literal short-pair profiles. The two choices are disjoint, including
repeated primes; all moving box and pool endpoints remain literal. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ShortPairProfilesWork
open LongerTupleActualProfiles
open LongerTupleEncoding (Representation)
open ShortPairSplitWork LongerTupleProfile SieveGeometricGrid SieveBoxedFamily
open SieveWeightedCutoffs UpperAfter545Remaining UpperAfter545Sectors
open ShortSingletonMasks ShortSingletonEndpoints

def chosen (X : ℝ) (second : Bool) (r : Representation) : Prop :=
  (prime second r : ℝ) ≤ X^(8/35:ℝ) ∧
    (second = true ∨ X^(8/35:ℝ) < ((drop second r).2.2 : ℝ))

def pairSource (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) : Finset Representation :=
  (source X s P z true js).filter (chosen X second)

def pairSupport (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) : Finset PairRep :=
  (pairSource X s P z second js).image (drop second)

def selectedIndex (second : Bool) (js : List ℕ) : ℕ :=
  js.getD (if second then 1 else 0) 0

def pairWeight (X s : ℝ) (a : PairRep) : ℂ :=
  (SieveSmallWeights.weight ((level X s/a.1)^s) ((level X s/a.1)^(s^2)) true a.2.1 : ℝ)
def pairLo (X s : ℝ) (second : Bool) (js : List ℕ) (a : PairRep) : ℕ :=
  gridLo (level X s/a.1) s (selectedIndex second js)
def pairHi (X s : ℝ) (z : ℝ → ℝ) (second : Bool) (js : List ℕ) (a : PairRep) : ℕ :=
  truncatedHi (level X s/a.1) s (z a.1) (selectedIndex second js)

def pairKernel (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ p ∈ P, ∑ d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s,
    ∑ t ∈ (family true (level X s/p) s (z p)).filter
      (fun t => indices (level X s/p) s t = js ∧ chosen X second (p,d,t)),
      SieveSmallWeights.weight ((level X s/p)^s) ((level X s/p)^(s^2)) true d *
        highKernel X f (p*(d*t.prod))

def pairMaskedSum (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (L R : ℝ) : ℂ :=
  LongerTupleMaskedCollection.maskedSum (pairSupport X s P z second js)
    ShortPairSplitWork.index (primeSupport X) (pairWeight X s)
    (pairLo X s second js) (pairHi X s z second js) (physicalCut X) L R

theorem pairSource_length (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (hjs : js.length = 2) (r : Representation)
    (hr : r ∈ pairSource X s P z second js) : r.2.2.length = 2 :=
  (source_length X s P z true js r (Finset.mem_filter.mp hr).1).trans hjs

theorem pairSource_prime_mem (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (hjs : js.length = 2) (hX : 0 ≤ X)
    (hs : 0 < s) (hg : BandGeometry X s P z) (r : Representation)
    (hr : r ∈ pairSource X s P z second js) : prime second r ∈ primeSupport X := by
  obtain ⟨hr,hchosen⟩ := Finset.mem_filter.mp hr
  have hm := source_matches X s P z true js hs hg r hr
  have hp := (mem_source X s P z true js r).mp hr |>.1
  have hpool := matches_pool _ s _ (hg r.1 hp).2.2.1 hs r.2.2 js hm
    (prime second r) (prime_mem second r ((source_length X s P z true js r hr).trans hjs))
  exact (mem_primeSupport X _ hX).mpr ⟨((mem_pool _ s _ _).mp hpool).1,hchosen.1⟩

theorem matches_replace_pair (D s z : ℝ) (second : Bool) (r : Representation)
    (js : List ℕ) (hjs : js.length = 2) (hm : Matches D s z r.2.2 js) (q : ℕ) :
    Matches D s z (rebuild second (drop second r) q).2.2 js ↔
      q.Prime ∧ InBox D s (q:ℝ) (selectedIndex second js) ∧ (q:ℝ) < z := by
  rcases r with ⟨p,d,t⟩
  obtain ⟨u,v,rfl⟩ := List.length_eq_two.mp (hm.length_eq.trans hjs)
  obtain ⟨i,j,rfl⟩ := List.length_eq_two.mp hjs
  have hu := (List.forall₂_cons.mp hm).1
  have hv := (List.forall₂_cons.mp (List.forall₂_cons.mp hm).2).1
  cases second <;> simp [Matches,rebuild,drop,selectedIndex,hu,hv]

theorem completion_iff (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (hjs : js.length = 2) (hX : 0 ≤ X)
    (hs : 0 < s) (hg : BandGeometry X s P z) (a : PairRep)
    (ha : a ∈ pairSupport X s P z second js) (q : ℕ) (hq : q ∈ primeSupport X) :
    rebuild second a q ∈ pairSource X s P z second js ↔
      InBox (level X s/a.1) s (q:ℝ) (selectedIndex second js) ∧ (q:ℝ) < z a.1 ∧
        X^(109/200:ℝ) < ((ShortPairSplitWork.index a*q : ℕ):ℝ) := by
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨hsource,hchosen⟩ := Finset.mem_filter.mp hr
  obtain ⟨hp,hd,ht,he,_⟩ := (mem_source X s P z true js r).mp hsource
  have hgeom := hg r.1 hp
  have hm := source_matches X s P z true js hs hg r hsource
  have hfixed := (family_fixed_iff true _ s _ hgeom.2.2.1 hs hgeom.2.2.2 r.2.2 js).mp ⟨ht,he⟩
  have hreplace := matches_replace_pair _ s _ second r js hjs hm q
  have hqshort := ((mem_primeSupport X q hX).mp hq).2
  have hchosenNew : chosen X second (rebuild second (drop second r) q) := by
    unfold chosen
    rw [prime_rebuild,drop_rebuild]
    exact ⟨hqshort,hchosen.2⟩
  constructor
  · intro hnew
    have hn := (mem_source X s P z true js _).mp (Finset.mem_filter.mp hnew).1
    have hmn := ((family_fixed_iff true _ s _ hgeom.2.2.1 hs hgeom.2.2.2
      (rebuild second (drop second r) q).2.2 js).mp ⟨hn.2.2.1,hn.2.2.2.1⟩).2
    have hb := hreplace.mp hmn
    exact ⟨hb.2.1,hb.2.2,by simpa only [ShortPairSplitWork.index_rebuild] using hn.2.2.2.2⟩
  · rintro ⟨hb,hz,hh⟩
    have hmn := hreplace.mpr ⟨((mem_primeSupport X q hX).mp hq).1,hb,hz⟩
    have hfn := (family_fixed_iff true _ s _ hgeom.2.2.1 hs hgeom.2.2.2
      (rebuild second (drop second r) q).2.2 js).mpr ⟨hfixed.1,hmn⟩
    apply Finset.mem_filter.mpr
    exact ⟨(mem_source X s P z true js _).mpr
      ⟨hp,hd,hfn.1,hfn.2,by simpa only [ShortPairSplitWork.index_rebuild] using hh⟩,hchosenNew⟩

theorem pairSupport_index_pos (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (hjs : js.length = 2) (hX : 0 < X)
    (a : PairRep) (ha : a ∈ pairSupport X s P z second js) : 0 < ShortPairSplitWork.index a := by
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ha
  have hh := (mem_source X s P z true js r).mp (Finset.mem_filter.mp hr).1 |>.2.2.2.2
  have hpos : 0 < LongerTupleEncoding.index r := by
    exact_mod_cast (Real.rpow_pos_of_pos hX (109/200:ℝ)).trans hh
  rw [index_drop second r (pairSource_length X s P z second js hjs r hr)] at hpos
  exact Nat.pos_of_mul_pos_right hpos

theorem pairSupport_cutoff_pos (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (hjs : js.length = 2) (hs : 0 < s)
    (hg : BandGeometry X s P z) (a : PairRep)
    (ha : a ∈ pairSupport X s P z second js) : 0 < z a.1 := by
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ha
  have hsource := (Finset.mem_filter.mp hr).1
  have hp := (mem_source X s P z true js r).mp hsource |>.1
  have hm := source_matches X s P z true js hs hg r hsource
  have hpool := matches_pool _ s _ (hg r.1 hp).2.2.1 hs r.2.2 js hm
    (prime second r) (prime_mem second r (pairSource_length X s P z second js hjs r hr))
  have hq := (mem_pool _ s _ _).mp hpool
  exact (by exact_mod_cast hq.1.pos : (0:ℝ) < prime second r).trans hq.2.1

theorem pairKernel_eq_source (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (f : ℕ → ℝ) :
    (pairKernel X s P z second js f : ℂ) =
      ∑ r ∈ pairSource X s P z second js, originalWeight X s true r *
        (f (LongerTupleEncoding.index r):ℂ) := by
  rw [pairSource,Finset.sum_filter,source_sum]
  unfold pairKernel
  simp only [Complex.ofReal_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro t _
  by_cases he : indices (level X s/p) s t = js <;>
    by_cases hc : chosen X second (p,d,t) <;>
    by_cases hh : X^(109/200:ℝ) < ((p*(d*t.prod):ℕ):ℝ) <;>
    simp only [originalWeight,LongerTupleEncoding.index,highKernel,Nat.mul_assoc,
      he,hc,hh,and_true,and_false,ite_true,ite_false,mul_zero,Complex.ofReal_mul,Complex.ofReal_zero]

theorem pairKernel_eq_masked (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (hjs : js.length = 2) (hX : 1 < X)
    (hs : 0 < s) (hg : BandGeometry X s P z) (L R : ℝ) :
    (pairKernel X s P z second js (floorKernel L R):ℂ) = pairMaskedSum X s P z second js L R := by
  rw [pairKernel_eq_source,completion_sum second (pairSource X s P z second js) (primeSupport X)
    (pairSource_length X s P z second js hjs)
    (pairSource_prime_mem X s P z second js hjs (by linarith) hs hg)]
  unfold pairMaskedSum LongerTupleMaskedCollection.maskedSum
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro q hq
  have hcomp := completion_iff X s P z second js hjs (by linarith) hs hg a ha q hq
  have hp : a.1 ∈ P := by
    obtain ⟨r,hr,he⟩ := Finset.mem_image.mp ha
    rw [←he]
    exact ((mem_source X s P z true js r).mp (Finset.mem_filter.mp hr).1).1
  have hgeom := hg a.1 hp
  have he := box_pool_high_prefix X (level X s/a.1) s (z a.1) (selectedIndex second js)
    (ShortPairSplitWork.index a) q (by linarith) (by linarith [hgeom.2.2.1])
    (pairSupport_cutoff_pos X s P z second js hjs hs hg a ha)
    (pairSupport_index_pos X s P z second js hjs (by linarith) a ha)
  simp only [hcomp,ShortPairSplitWork.index_rebuild]
  change (if _ then pairWeight X s a * _ else 0) = _
  simp only [pairHi,pairLo]
  rw [←he]
  by_cases hc : InBox (level X s/a.1) s (q:ℝ) (selectedIndex second js) ∧ (q:ℝ) < z a.1 ∧
    X^(109/200:ℝ) < ((ShortPairSplitWork.index a*q:ℕ):ℝ)
  · simp [hc]
  · simp only [hc,ite_false,mul_zero,zero_mul]

#print axioms pairKernel_eq_masked
run_cmd do
  for decl in [``pairSource_length, ``pairSource_prime_mem, ``matches_replace_pair,
      ``completion_iff, ``pairSupport_index_pos, ``pairSupport_cutoff_pos,
      ``pairKernel_eq_source, ``pairKernel_eq_masked] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "LITERAL SHORT PAIR PROFILE MASK ADAPTER PASSED"

end ShortPairProfilesWork
