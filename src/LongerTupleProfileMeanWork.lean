import LongerTupleActualProfilesWork
import LongerTupleGlobalMean

/-! Apply the generic masked estimate to a literal higher profile. Relations
are defined by actual completions before Fourier expansion. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LongerTupleProfileMeanWork
open LongerTupleActualProfiles LongerTupleEncoding LongerTupleThirdSplit
open LongerTupleProfile LongerTupleCollection ShortSingletonEndpoints
open ShortSingletonMasks UpperAfter545Remaining SieveWeightedCutoffs

def completionRelation (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (outer : Bool) (js : List ℕ) (m q : ℕ) : Prop :=
  ∃ a ∈ actualSupport X s P z outer js,
    LongerTupleEncoding.index a = m ∧ rebuild a q ∈ source X s P z outer js

theorem actual_index_bounds (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (outer : Bool) (js : List ℕ) (hjs : 3 ≤ js.length) (hX : 1 < X)
    (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X)
    (hg : BandGeometry X s P z) (a : Representation)
    (ha : a ∈ actualSupport X s P z outer js) :
    2 ≤ LongerTupleEncoding.index a ∧ (LongerTupleEncoding.index a : ℝ) ≤ X := by
  have hpos := support_index_pos X s P z outer js hjs (by linarith) a ha
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ha
  have hp := (mem_source X s P z outer js r).mp hr |>.1
  have hp2 := (hg r.1 hp).1
  have hdiv : r.1 ∣ LongerTupleEncoding.index (drop r) := by
    simpa only [LongerTupleEncoding.index, drop, Nat.mul_assoc] using
      (dvd_mul_right r.1 (r.2.1 * (erase r.2.2).prod))
  have hlen := source_length X s P z outer js r hr
  have ht := source_third_bounds X s P z outer js hjs hX hs hs1 hlog hg r hr
  have hle : LongerTupleEncoding.index (drop r) ≤ LongerTupleEncoding.index r := by
    rw [index_drop r (by omega)]
    exact Nat.le_mul_of_pos_right _ ht.1.pos
  refine ⟨hp2.trans (Nat.le_of_dvd hpos hdiv), ?_⟩
  have hphysical := source_physical_bound X s P z outer js hjs hX hs hs1 hg r hr
  have htop : X^(1-3*s/2) ≤ X := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX.le (show 1-3*s/2 ≤ (1:ℝ) by linarith)
  exact (show (LongerTupleEncoding.index (drop r) : ℝ) ≤
    (LongerTupleEncoding.index r : ℝ) by exact_mod_cast hle).trans (hphysical.le.trans htop)

theorem relation_bounds (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (outer : Bool) (js : List ℕ) (hjs : 3 ≤ js.length) (hX : 1 < X)
    (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X)
    (hg : BandGeometry X s P z) (m q : ℕ)
    (hr : completionRelation X s P z outer js m q) :
    X^(109/200:ℝ) < (m:ℝ)*(q:ℝ) ∧ (m:ℝ)*(q:ℝ) < X^(1-3*s/2) ∧
      X^((49/100:ℝ)*s^2) ≤ (q:ℝ) ∧ (q:ℝ) ≤ X^(8/35:ℝ) := by
  obtain ⟨a,ha,he,hcomp⟩ := hr
  have hlen : 2 ≤ a.2.2.length := by
    rw [support_length X s P z outer js hjs a ha]
    omega
  have hhigh := (mem_source X s P z outer js (rebuild a q)).mp hcomp |>.2.2.2.2
  have hphysical := source_physical_bound X s P z outer js hjs hX hs hs1 hg
    (rebuild a q) hcomp
  have hthird := source_third_bounds X s P z outer js hjs hX hs hs1 hlog hg
    (rebuild a q) hcomp
  rw [third_rebuild a q hlen] at hthird
  rw [index_rebuild, he, Nat.cast_mul] at hhigh hphysical
  exact ⟨hhigh,hphysical,hthird.2.1,hthird.2.2.le.trans
    (Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num))⟩

theorem mask_zero_off_relation (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (outer : Bool) (js : List ℕ) (hjs : 3 ≤ js.length) (hX : 1 < X)
    (hs : 0 < s) (hg : BandGeometry X s P z) (a : Representation)
    (ha : a ∈ actualSupport X s P z outer js) (q : ℕ) (hq : q ∈ primeSupport X)
    (hn : ¬completionRelation X s P z outer js (LongerTupleEncoding.index a) q) :
    (prefixIndicator (hi X s z js a) q - prefixIndicator (lo X s js a) q) *
      (1-prefixIndicator (physicalCut X (LongerTupleEncoding.index a)) q) = 0 := by
  have hqp := ((mem_primeSupport X q (by linarith)).mp hq).1
  have hnot : rebuild a q ∉ source X s P z outer js := by
    intro hc
    exact hn ⟨a,ha,rfl,hc⟩
  have hcomp := completion_iff X s P z outer js hjs hs hg a ha q hqp
  have hp : a.1 ∈ P := by
    obtain ⟨r,hr,he⟩ := Finset.mem_image.mp ha
    rw [←he]
    exact ((mem_source X s P z outer js r).mp hr).1
  have hgeom := hg a.1 hp
  have hmask := box_pool_high_prefix X (level X s/a.1) s (z a.1) (third js)
    (LongerTupleEncoding.index a) q (by linarith) (by linarith [hgeom.2.2.1])
    (support_cutoff_pos X s P z outer js hjs hs hg a ha)
    (support_index_pos X s P z outer js hjs (by linarith) a ha)
  have hncond := fun hc => hnot (hcomp.mpr hc)
  simpa only [hi,lo,ite_eq_right hncond] using hmask.symm

/-- For fixed deleted tuple length, the saving and threshold are uniform
over both modes, profiles, and all prime-band data satisfying literal geometry. -/
theorem eventually_profile_square (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1/1000)
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, 1 < X ∧ 1000 ≤ Real.log X ∧
      ∀ (P : Finset ℕ) (z : ℝ → ℝ) (outer : Bool) (js : List ℕ),
        js.length = k+1 → BandGeometry X s P z →
        let Y : ℝ := X^(101/1000:ℝ)/2
        (1/X)*(∫ x in Icc X (2*X),
          profileKernel X s P z outer js (floorKernel (x-x*(Y/X)) x)^2) ≤ Y^2*X^(-c) := by
  obtain ⟨c,hc,hmean⟩ := LongerTupleGlobalMean.eventually_bound
    (α := Representation) s hs hs1 (k+2)
  refine ⟨c,hc,?_⟩
  filter_upwards [hmean, eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1000)] with X hm hX hlog
  refine ⟨hX,hlog,?_⟩
  intro P z outer js hlen hg
  dsimp only
  have hjs : 3 ≤ js.length := by omega
  have hlength : ∀ a ∈ actualSupport X s P z outer js, a.2.2.length = k := by
    intro a ha
    rw [support_length X s P z outer js hjs a ha, hlen]
    omega
  have hb := hm.2 (actualSupport X s P z outer js) LongerTupleEncoding.index
    (LongerTupleEncoding.encode k) (primeSupport X)
    (completionRelation X s P z outer js) (primeCutoff X) (originalWeight X s outer)
    (lo X s js) (hi X s z js) (physicalCut X)
    (fun a ha => encode_product k a (hlength a ha))
    (fun a ha b hb he => encode_injective k a b (hlength a ha) (hlength b hb) he)
    (by
      intro m hm
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hm
      exact actual_index_bounds X s P z outer js hjs hX hs hs1 hlog hg a ha)
    (fun q hq => ⟨(primeSupport_bounds X hX.le q hq).1,
      (primeSupport_bounds X hX.le q hq).2.1⟩)
    (fun q hq => (primeSupport_bounds X hX.le q hq).2.2)
    (primeCutoff_le X hX.le) (fun a _ => originalWeight_norm_le X s outer a)
    (fun m _ q _ hr => relation_bounds X s P z outer js hjs hX hs hs1 hlog hg m q hr)
    (fun a ha q hq hn => mask_zero_off_relation X s P z outer js hjs hX hs hg a ha q hq hn)
  have heq : (fun x : ℝ => profileKernel X s P z outer js
      (floorKernel (x-x*((X^(101/1000:ℝ)/2)/X)) x)^2) =
      (fun x => (profileMaskedSum X s P z outer js
        (x-x*((X^(101/1000:ℝ)/2)/X)) x).re^2) := by
    funext x
    have he := congrArg Complex.re
      (profileKernel_eq_masked X s P z outer js hjs hX hs hs1 hlog hg
        (x-x*((X^(101/1000:ℝ)/2)/X)) x)
    simpa only [Complex.ofReal_re] using congrArg (fun r : ℝ => r^2) he
  rw [heq]
  exact hb

#print axioms eventually_profile_square
run_cmd do
  for decl in [``actual_index_bounds, ``relation_bounds, ``mask_zero_off_relation,
      ``eventually_profile_square] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "LITERAL HIGHER PROFILE SECOND MEAN PASSED"

end LongerTupleProfileMeanWork
