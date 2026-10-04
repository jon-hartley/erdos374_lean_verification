import LongerTupleProfile
import LongerTupleGeometry
import LongerTupleEncoding
import LongerTupleThirdSplit
import LongerTupleMaskedCollection

/-! Literal higher upper-tuple profiles. The first-factor support is the
image of actual physically high completions after deleting the third prime.
Both prime bands use their original moving cutoff and small sieve weights. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LongerTupleActualProfiles
open SieveWeightedCutoffs SieveUpperBoxing SieveGeometricGrid SieveBoxedFamily
open LongerTupleProfile LongerTupleEncoding LongerTupleThirdSplit
open UpperAfter545Sectors UpperAfter545Remaining PositiveSharpBoxedCount
open ShortSingletonEndpoints ShortSingletonMasks

def family (outer : Bool) (D s z : ℝ) : Finset (List ℕ) :=
  (if outer then outerFamily else innerFamily) D s z

def profiles (outer : Bool) (s : ℝ) : Finset (List ℕ) :=
  if outer then outerProfiles s else innerProfiles s

def primeCutoff (X : ℝ) : ℕ := Nat.floor (X ^ (8/35 : ℝ))
def primeSupport (X : ℝ) : Finset ℕ :=
  (Finset.range (primeCutoff X + 1)).filter Nat.Prime

def source (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (outer : Bool)
    (js : List ℕ) : Finset Representation :=
  P.biUnion (fun p => (SieveUpperBoxWindow.smallCarrier (level X s/p) s).biUnion
    (fun d => ((family outer (level X s/p) s (z p)).filter
      (fun t => indices (level X s/p) s t = js ∧
        X ^ (109/200 : ℝ) < ((p*d*t.prod : ℕ) : ℝ))).image (fun t => (p,d,t))))

def actualSupport (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (outer : Bool)
    (js : List ℕ) : Finset Representation :=
  (source X s P z outer js).image LongerTupleThirdSplit.drop

def originalWeight (X s : ℝ) (outer : Bool) (a : Representation) : ℂ :=
  (SieveSmallWeights.weight ((level X s/a.1)^s) ((level X s/a.1)^(s^2)) outer a.2.1 : ℝ)

def lo (X s : ℝ) (js : List ℕ) (a : Representation) : ℕ :=
  gridLo (level X s/a.1) s (third js)

def hi (X s : ℝ) (z : ℝ → ℝ) (js : List ℕ) (a : Representation) : ℕ :=
  truncatedHi (level X s/a.1) s (z a.1) (third js)

def profileKernel (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (outer : Bool)
    (js : List ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ p ∈ P, ∑ d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s,
    ∑ t ∈ (family outer (level X s/p) s (z p)).filter
      (fun t => indices (level X s/p) s t = js),
      SieveSmallWeights.weight ((level X s/p)^s) ((level X s/p)^(s^2)) outer d *
        highKernel X f (p*(d*t.prod))

def profileMaskedSum (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (outer : Bool)
    (js : List ℕ) (L R : ℝ) : ℂ :=
  LongerTupleMaskedCollection.maskedSum (actualSupport X s P z outer js)
    LongerTupleEncoding.index (primeSupport X) (originalWeight X s outer)
    (lo X s js) (hi X s z js) (physicalCut X) L R

def BandGeometry (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) : Prop :=
  ∀ p ∈ P, 2 ≤ p ∧ (p : ℝ) ≤ Real.sqrt (2*X) ∧ 1 < level X s/p ∧
    z p ≤ level X s/p

theorem family_mem_or (outer : Bool) (D s z : ℝ) (t : List ℕ)
    (ht : t ∈ family outer D s z) :
    t ∈ outerFamily D s z ∨ t ∈ innerFamily D s z := by
  cases outer with
  | false => exact Or.inr ht
  | true => exact Or.inl ht

theorem family_fixed_iff (outer : Bool) (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hz : z ≤ D) (t js : List ℕ) :
    t ∈ family outer D s z ∧ indices D s t = js ↔
      js ∈ profiles outer s ∧ Matches D s z t js := by
  cases outer with
  | false => exact inner_fixed_profile_iff D s z hD hs hz t js
  | true => exact outer_fixed_profile_iff D s z hD hs hz t js

theorem mem_primeSupport (X : ℝ) (q : ℕ) (hX : 0 ≤ X) :
    q ∈ primeSupport X ↔ q.Prime ∧ (q : ℝ) ≤ X ^ (8/35 : ℝ) := by
  simp only [primeSupport, primeCutoff, Finset.mem_filter, Finset.mem_range,
    Nat.lt_succ_iff, Nat.le_floor_iff (Real.rpow_nonneg hX _)]
  exact and_comm

theorem primeSupport_bounds (X : ℝ) (hX : 1 ≤ X) (q : ℕ) (hq : q ∈ primeSupport X) :
    2 ≤ q ∧ (q : ℝ) ≤ X ∧ q ≤ primeCutoff X := by
  have hh := (mem_primeSupport X q (by linarith)).mp hq
  exact ⟨hh.1.two_le, hh.2.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX
      (show (8/35 : ℝ) ≤ 1 by norm_num)),
    Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hq).1)⟩

theorem primeCutoff_le (X : ℝ) (hX : 1 ≤ X) : (primeCutoff X : ℝ) ≤ X := by
  exact (Nat.floor_le (Real.rpow_nonneg (by linarith) _)).trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX
      (show (8/35 : ℝ) ≤ 1 by norm_num))

theorem mem_source (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (outer : Bool)
    (js : List ℕ) (a : Representation) : a ∈ source X s P z outer js ↔
      a.1 ∈ P ∧ a.2.1 ∈ SieveUpperBoxWindow.smallCarrier (level X s/a.1) s ∧
      a.2.2 ∈ family outer (level X s/a.1) s (z a.1) ∧
      indices (level X s/a.1) s a.2.2 = js ∧
      X ^ (109/200 : ℝ) < (LongerTupleEncoding.index a : ℝ) := by
  rcases a with ⟨p,d,t⟩
  simp [source, LongerTupleEncoding.index, and_assoc]

theorem source_matches (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (outer : Bool)
    (js : List ℕ) (hs : 0 < s) (hg : BandGeometry X s P z)
    (a : Representation) (ha : a ∈ source X s P z outer js) :
    Matches (level X s/a.1) s (z a.1) a.2.2 js := by
  obtain ⟨hp, _, ht, he, _⟩ := (mem_source X s P z outer js a).mp ha
  have hpgeom := hg a.1 hp
  exact ((family_fixed_iff outer _ s _ hpgeom.2.2.1 hs hpgeom.2.2.2 a.2.2 js).mp
    ⟨ht,he⟩).2

theorem source_length (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (outer : Bool)
    (js : List ℕ) (a : Representation) (ha : a ∈ source X s P z outer js) :
    a.2.2.length = js.length := by
  have he := (mem_source X s P z outer js a).mp ha |>.2.2.2.1
  simpa only [indices, List.length_map] using congrArg List.length he

theorem source_third_bounds (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (outer : Bool)
    (js : List ℕ) (hjs : 3 ≤ js.length) (hX : 1 < X) (hs : 0 < s)
    (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) (hg : BandGeometry X s P z)
    (a : Representation) (ha : a ∈ source X s P z outer js) :
    (third a.2.2).Prime ∧ X ^ ((49/100 : ℝ)*s^2) ≤ (third a.2.2 : ℝ) ∧
      (third a.2.2 : ℝ) < X ^ (201/1000 : ℝ) := by
  obtain ⟨hp, _, ht, _, _⟩ := (mem_source X s P z outer js a).mp ha
  have hlen : 3 ≤ a.2.2.length := by rw [source_length X s P z outer js a ha]; exact hjs
  obtain ⟨u,v,q,tail,he⟩ := exists_three a.2.2 hlen
  have hpgeom := hg a.1 hp
  have hh := LongerTupleGeometry.third_prime_bounds X s (z a.1) a.1 u v q tail
    hX hs hs1 hlog (by omega) hpgeom.2.1 hpgeom.2.2.1 hpgeom.2.2.2
    (by simpa only [he] using family_mem_or outer _ s _ a.2.2 ht)
  simpa [he, third] using hh

theorem source_third_mem (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (outer : Bool)
    (js : List ℕ) (hjs : 3 ≤ js.length) (hX : 1 < X) (hs : 0 < s)
    (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) (hg : BandGeometry X s P z)
    (a : Representation) (ha : a ∈ source X s P z outer js) :
    third a.2.2 ∈ primeSupport X := by
  have hh := source_third_bounds X s P z outer js hjs hX hs hs1 hlog hg a ha
  exact (mem_primeSupport X _ (by linarith)).mpr ⟨hh.1, hh.2.2.le.trans
    (Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num))⟩

theorem source_physical_bound (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (outer : Bool)
    (js : List ℕ) (hjs : 3 ≤ js.length) (hX : 1 < X) (hs : 0 < s)
    (hs1 : s ≤ 1/1000) (hg : BandGeometry X s P z)
    (a : Representation) (ha : a ∈ source X s P z outer js) :
    (LongerTupleEncoding.index a : ℝ) < X ^ (1-3*s/2) := by
  obtain ⟨hp, hd, ht, _, _⟩ := (mem_source X s P z outer js a).mp ha
  have hpgeom := hg a.1 hp
  have hlen := source_length X s P z outer js a ha
  exact LongerTupleGeometry.physical_product_lt X s (z a.1) a.1 a.2.1 a.2.2
    hX hs hs1 (by omega) hpgeom.2.2.1 hpgeom.2.2.2 hd
    (by intro he; simp only [he, List.length_nil] at hlen; omega)
    (family_mem_or outer _ s _ a.2.2 ht)

theorem matches_replace_third (D s z : ℝ) (t js : List ℕ) (hjs : 3 ≤ js.length)
    (ht : Matches D s z t js) (q : ℕ) :
    Matches D s z (LongerTupleThirdSplit.insert q (erase t)) js ↔
      q.Prime ∧ InBox D s (q : ℝ) (third js) ∧ (q : ℝ) < z := by
  have hlen : 3 ≤ t.length := by rw [ht.length_eq]; exact hjs
  obtain ⟨a,b,c,tail,rfl⟩ := exists_three t hlen
  obtain ⟨j0,j1,j,jtail,rfl⟩ := exists_three js hjs
  have hh := List.forall₂_cons.mp ht
  have hh1 := List.forall₂_cons.mp hh.2
  have hh2 := List.forall₂_cons.mp hh1.2
  have hl : Matches D s z [a,b] [j0,j1] :=
    List.Forall₂.cons hh.1 (List.Forall₂.cons hh1.1 List.Forall₂.nil)
  simpa [LongerTupleThirdSplit.insert, erase, third] using
    matches_insert_iff D s z [a,b] tail [j0,j1] jtail q j hl hh2.2

theorem index_rebuild (a : Representation) (q : ℕ) :
    LongerTupleEncoding.index (rebuild a q) = LongerTupleEncoding.index a * q := by
  have hp := List.prod_take_mul_prod_drop a.2.2 2
  simp only [LongerTupleEncoding.index, rebuild, LongerTupleThirdSplit.insert, List.prod_append, List.prod_cons]
  rw [←hp]
  ring

theorem support_length (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (outer : Bool)
    (js : List ℕ) (hjs : 3 ≤ js.length) (a : Representation)
    (ha : a ∈ actualSupport X s P z outer js) : a.2.2.length = js.length - 1 := by
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ha
  have hlen := source_length X s P z outer js r hr
  have hh := erase_length r.2.2 (by omega)
  change (erase r.2.2).length = js.length - 1
  omega

theorem support_index_pos (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (outer : Bool)
    (js : List ℕ) (hjs : 3 ≤ js.length) (hX : 0 < X) (a : Representation)
    (ha : a ∈ actualSupport X s P z outer js) : 0 < LongerTupleEncoding.index a := by
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ha
  have hlen := source_length X s P z outer js r hr
  have hh := (mem_source X s P z outer js r).mp hr |>.2.2.2.2
  have hrpos : 0 < LongerTupleEncoding.index r := by
    exact_mod_cast (Real.rpow_pos_of_pos hX (109/200 : ℝ)).trans hh
  rw [index_drop r (by omega)] at hrpos
  exact Nat.pos_of_mul_pos_right hrpos

theorem completion_iff (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (outer : Bool)
    (js : List ℕ) (hjs : 3 ≤ js.length) (hs : 0 < s) (hg : BandGeometry X s P z)
    (a : Representation) (ha : a ∈ actualSupport X s P z outer js)
    (q : ℕ) (hqp : q.Prime) :
    rebuild a q ∈ source X s P z outer js ↔
      InBox (level X s/a.1) s (q : ℝ) (third js) ∧ (q : ℝ) < z a.1 ∧
        X ^ (109/200 : ℝ) < ((LongerTupleEncoding.index a*q : ℕ) : ℝ) := by
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨hp,hd,ht,he,_⟩ := (mem_source X s P z outer js r).mp hr
  have hpgeom := hg r.1 hp
  have hm := source_matches X s P z outer js hs hg r hr
  have hfixed := (family_fixed_iff outer _ s _ hpgeom.2.2.1 hs hpgeom.2.2.2 r.2.2 js).mp
    ⟨ht,he⟩
  have hreplace := matches_replace_third _ s _ r.2.2 js hjs hm q
  constructor
  · intro hnew
    have hn := (mem_source X s P z outer js _).mp hnew
    have hmnew := ((family_fixed_iff outer _ s _ hpgeom.2.2.1 hs hpgeom.2.2.2
      (LongerTupleThirdSplit.insert q (erase r.2.2)) js).mp ⟨hn.2.2.1,hn.2.2.2.1⟩).2
    have hqbox := hreplace.mp hmnew
    exact ⟨hqbox.2.1,hqbox.2.2,by simpa only [index_rebuild] using hn.2.2.2.2⟩
  · rintro ⟨hb,hz,hh⟩
    have hmnew := hreplace.mpr ⟨hqp,hb,hz⟩
    have hfnew := (family_fixed_iff outer _ s _ hpgeom.2.2.1 hs hpgeom.2.2.2
      (LongerTupleThirdSplit.insert q (erase r.2.2)) js).mpr ⟨hfixed.1,hmnew⟩
    exact (mem_source X s P z outer js _).mpr
      ⟨hp,hd,hfnew.1,hfnew.2,by simpa only [index_rebuild] using hh⟩

theorem support_cutoff_pos (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (outer : Bool)
    (js : List ℕ) (hjs : 3 ≤ js.length) (hs : 0 < s) (hg : BandGeometry X s P z)
    (a : Representation) (ha : a ∈ actualSupport X s P z outer js) :
    0 < z a.1 := by
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ha
  have hm := source_matches X s P z outer js hs hg r hr
  have hlen := source_length X s P z outer js r hr
  obtain ⟨u,v,q,tail,he⟩ := exists_three r.2.2 (by omega)
  have hp := matches_pool _ s _ (hg r.1 ((mem_source X s P z outer js r).mp hr).1).2.2.1
    hs r.2.2 js hm q (by simp [he])
  have hq := (mem_pool _ s _ q).mp hp
  exact (by exact_mod_cast hq.1.pos : (0 : ℝ) < q).trans hq.2.1

theorem source_sum (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (outer : Bool)
    (js : List ℕ) (f : Representation → ℂ) :
    (∑ a ∈ source X s P z outer js, f a) =
      ∑ p ∈ P, ∑ d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s,
        ∑ t ∈ (family outer (level X s/p) s (z p)).filter
          (fun t => indices (level X s/p) s t = js ∧
            X ^ (109/200 : ℝ) < ((p*d*t.prod : ℕ) : ℝ)), f (p,d,t) := by
  unfold source
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_biUnion]
    · apply Finset.sum_congr rfl
      intro d _
      exact Finset.sum_image (fun t _ u _ he => (Prod.mk.inj (Prod.mk.inj he).2).2)
    · intro d _ e _ hde
      apply Finset.disjoint_left.mpr
      intro a ha hb
      obtain ⟨t,_,ht⟩ := Finset.mem_image.mp ha
      obtain ⟨u,_,hu⟩ := Finset.mem_image.mp hb
      exact hde (Prod.mk.inj (Prod.mk.inj (ht.trans hu.symm)).2).1
  · intro p _ q _ hpq
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨d,_,hd⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨e,_,he⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨t,_,ht⟩ := Finset.mem_image.mp hd
    obtain ⟨u,_,hu⟩ := Finset.mem_image.mp he
    exact hpq (Prod.mk.inj (ht.trans hu.symm)).1

theorem profileKernel_eq_source (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (outer : Bool)
    (js : List ℕ) (f : ℕ → ℝ) :
    (profileKernel X s P z outer js f : ℂ) =
      ∑ a ∈ source X s P z outer js, originalWeight X s outer a *
        (f (LongerTupleEncoding.index a) : ℂ) := by
  rw [source_sum]
  unfold profileKernel
  simp only [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro d _
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  by_cases he : indices (level X s/p) s t = js <;>
    by_cases hh : X ^ (109/200 : ℝ) < ((p*(d*t.prod) : ℕ) : ℝ) <;>
    simp only [originalWeight, LongerTupleEncoding.index, highKernel,
      Nat.mul_assoc, he, hh, ite_true, ite_false, and_true, and_false,
      mul_zero, Complex.ofReal_mul, Complex.ofReal_zero]

theorem profileKernel_eq_masked (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ) (outer : Bool)
    (js : List ℕ) (hjs : 3 ≤ js.length) (hX : 1 < X) (hs : 0 < s)
    (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) (hg : BandGeometry X s P z)
    (L R : ℝ) : (profileKernel X s P z outer js (floorKernel L R) : ℂ) =
      profileMaskedSum X s P z outer js L R := by
  rw [profileKernel_eq_source, completion_sum (source X s P z outer js) (primeSupport X)
    (by intro a ha; rw [source_length X s P z outer js a ha]; exact hjs)
    (source_third_mem X s P z outer js hjs hX hs hs1 hlog hg)]
  unfold profileMaskedSum LongerTupleMaskedCollection.maskedSum
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro q hq
  have hqp := ((mem_primeSupport X q (by linarith)).mp hq).1
  have hcomp := completion_iff X s P z outer js hjs hs hg a ha q hqp
  have hp : a.1 ∈ P := by
    obtain ⟨r,hr,he⟩ := Finset.mem_image.mp ha
    rw [←he]
    exact ((mem_source X s P z outer js r).mp hr).1
  have hpgeom := hg a.1 hp
  have he := box_pool_high_prefix X (level X s/a.1) s (z a.1) (third js)
    (LongerTupleEncoding.index a) q (by linarith) (by linarith [hpgeom.2.2.1])
    (support_cutoff_pos X s P z outer js hjs hs hg a ha)
    (support_index_pos X s P z outer js hjs (by linarith) a ha)
  simp only [hcomp, index_rebuild]
  change (if _ then originalWeight X s outer a * _ else 0) = _
  simp only [hi, lo]
  rw [←he]
  by_cases hc : InBox (level X s/a.1) s (q : ℝ) (third js) ∧ (q : ℝ) < z a.1 ∧
    X ^ (109/200 : ℝ) < ((LongerTupleEncoding.index a*q : ℕ) : ℝ)
  · simp [hc]
  · simp only [hc, ite_false, mul_zero, zero_mul]

theorem originalWeight_norm_le (X s : ℝ) (outer : Bool) (a : Representation) :
    ‖originalWeight X s outer a‖ ≤ 1 := by
  rw [originalWeight, Complex.norm_real, Real.norm_eq_abs]
  exact SieveSmallWeights.weight_abs_le_one _ _ outer a.2.1

theorem large_band_geometry (X s : ℝ) (hX : 1 < X) (hs : 0 < s)
    (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) :
    BandGeometry X s (largePrimes X) (cutoffThree X s) := by
  intro p hp
  have hg := UpperAfter545Geometry.large_geometry X s p hX hs hs1 hlog hp
  exact ⟨(PositiveSharpSieveDecomposition.large_band_bounds X p hp).1.two_le, hg.2⟩

theorem small_band_geometry (X s : ℝ) (hX : 1 < X) (hs : 0 < s)
    (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) :
    BandGeometry X s (smallPrimes X s) (SieveCappedUpperMainTerms.cappedFourth X s) := by
  intro p hp
  have hg := UpperAfter545Geometry.small_geometry X s p hX hs hs1 hlog hp
  exact ⟨(PositiveSharpSieveDecomposition.small_band_bounds X s p hp).1.two_le, hg.2⟩

#print axioms profileKernel_eq_masked

run_cmd do
  for decl in [``family_mem_or, ``family_fixed_iff, ``mem_primeSupport,
      ``primeSupport_bounds, ``primeCutoff_le, ``mem_source, ``source_matches,
      ``source_length, ``source_third_bounds, ``source_third_mem, ``source_physical_bound,
      ``matches_replace_third, ``index_rebuild, ``support_length, ``support_index_pos,
      ``completion_iff, ``support_cutoff_pos, ``source_sum, ``profileKernel_eq_source,
      ``profileKernel_eq_masked,
      ``originalWeight_norm_le, ``large_band_geometry, ``small_band_geometry] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL COMPLETION-RESTRICTED HIGHER PROFILE SUPPORT GEOMETRY PASSED"

end LongerTupleActualProfiles
