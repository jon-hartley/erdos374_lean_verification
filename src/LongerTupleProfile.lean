import ShortSingletonEndpoints

/-! Exact fixed profiles for the literal upper tuple families. Numerical
acceptance is independent of the moving level D. Ordered lists retain all
repetitions. A pool-truncated box uses a clamped upper endpoint, so an empty
or reversed real interval contributes zero before the Fourier expansion. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LongerTupleProfile
open SieveGeometricGrid SieveBoxedFamily SieveBoxTuples
open ShortSingletonEndpoints ShortSingletonMasks

def numericAccepts (s T : ℝ) (upper : Bool) (u : ℝ) : List ℕ → Prop
  | [] => True
  | j :: js => (upper = false ∨ u + 3 * exponent s j < T) ∧
      numericAccepts s T (!upper) (u + exponent s j) js

def outerAdmissible (s : ℝ) (js : List ℕ) : Prop :=
  Even js.length ∧ js.Pairwise (· ≥ ·) ∧ numericAccepts s 1 true 0 js

def innerAdmissible (s : ℝ) (js : List ℕ) : Prop :=
  ¬Even js.length ∧ js.Pairwise (· > ·) ∧ numericAccepts s (1 / ratio s) true 0 js

def allProfiles (s : ℝ) : Finset (List ℕ) :=
  boundedTuples (Finset.range (SieveGeometricGrid.cutoff s + 1)) (SieveBoxLength.cutoff s)

def outerProfiles (s : ℝ) : Finset (List ℕ) := (allProfiles s).filter (outerAdmissible s)
def innerProfiles (s : ℝ) : Finset (List ℕ) := (allProfiles s).filter (innerAdmissible s)

def Matches (D s z : ℝ) (t js : List ℕ) : Prop :=
  List.Forall₂ (fun (q j : ℕ) => q.Prime ∧ InBox D s (q : ℝ) j ∧ (q : ℝ) < z) t js

theorem accepts_rpow_iff (D s T : ℝ) (hD : 1 < D) (upper : Bool) (u : ℝ)
    (js : List ℕ) :
    SieveBoxPrefix.accepts (D ^ T) upper (D ^ u) (js.map (scale D s)) ↔
      numericAccepts s T upper u js := by
  have hD0 : 0 < D := by linarith
  induction js generalizing upper u with
  | nil => rfl
  | cons j js ih =>
    have hcube : D ^ u * (scale D s j) ^ 3 = D ^ (u + 3 * exponent s j) := by
      rw [scale, ←Real.rpow_mul_natCast hD0.le, ←Real.rpow_add hD0]
      congr 1
      ring
    have hmul : D ^ u * scale D s j = D ^ (u + exponent s j) := by
      rw [scale, Real.rpow_add hD0]
    simp only [List.map_cons, SieveBoxPrefix.accepts, numericAccepts, hcube, hmul,
      Real.rpow_lt_rpow_left_iff hD, ih]

theorem scales_eq_profile (D s : ℝ) (t : List ℕ) :
    scales D s t = (indices D s t).map (scale D s) := by
  simp only [scales, indices, List.map_map]
  rfl

theorem outerTest_iff_numeric (D s : ℝ) (hD : 1 < D) (t : List ℕ) :
    SieveUpperBoxFamily.outerTest D s t ↔ outerAdmissible s (indices D s t) := by
  have ha := accepts_rpow_iff D s 1 hD true 0 (indices D s t)
  simp only [Real.rpow_one, Real.rpow_zero, ←scales_eq_profile] at ha
  simp only [SieveUpperBoxFamily.outerTest, outerAdmissible, indices, List.length_map]
  exact and_congr_right (fun _ => and_congr_right (fun _ => ha))

theorem innerTest_iff_numeric (D s : ℝ) (hD : 1 < D) (t : List ℕ) :
    SieveUpperBoxFamily.innerTest D s t ↔ innerAdmissible s (indices D s t) := by
  have ha := accepts_rpow_iff D s (1 / ratio s) hD true 0 (indices D s t)
  simp only [Real.rpow_zero, ←scales_eq_profile] at ha
  simp only [SieveUpperBoxFamily.innerTest, innerAdmissible, indices, List.length_map]
  exact and_congr_right (fun _ => and_congr_right (fun _ => ha))

theorem matches_indices (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (t js : List ℕ) (h : Matches D s z t js) : indices D s t = js := by
  induction h with
  | nil => rfl
  | @cons q j t js hq htail ih =>
    simpa only [indices, List.map_cons, boxIndex_eq_of_inBox D s q hD hs j hq.2.1]
      using congrArg (List.cons j) ih

theorem matches_pool (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (t js : List ℕ) (h : Matches D s z t js) : ∀ q ∈ t, q ∈ pool D s z := by
  induction h with
  | nil => simp
  | @cons q j t js hq htail ih =>
    intro r hr
    rcases List.mem_cons.mp hr with he | hr
    · subst r
      apply (mem_pool D s z q).mpr
      refine ⟨hq.1, hq.2.2, ?_⟩
      exact ((scale_zero D s).symm.trans_le
        ((scale_strictMono D s hD hs).monotone (Nat.zero_le j))).trans hq.2.1.1
    · exact ih r hr

theorem matches_of_pool (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (t : List ℕ) (hp : ∀ q ∈ t, q ∈ pool D s z) :
    Matches D s z t (indices D s t) := by
  induction t with
  | nil => exact List.Forall₂.nil
  | cons q t ih =>
    have hq := (mem_pool D s z q).mp (hp q (by simp))
    exact List.Forall₂.cons ⟨hq.1,
      boxIndex_spec D s q hD hs hq.2.2 (hq.2.1.trans_le hz), hq.2.1⟩
      (ih (fun r hr => hp r (by simp [hr])))

theorem matches_iff (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (t js : List ℕ) : Matches D s z t js ↔
      (∀ q ∈ t, q ∈ pool D s z) ∧ indices D s t = js := by
  constructor
  · intro h
    exact ⟨matches_pool D s z hD hs t js h, matches_indices D s z hD hs t js h⟩
  · rintro ⟨hp, rfl⟩
    exact matches_of_pool D s z hD hs hz t hp

theorem matches_unique (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (t js ks : List ℕ) (hj : Matches D s z t js) (hk : Matches D s z t ks) : js = ks :=
  (matches_indices D s z hD hs t js hj).symm.trans (matches_indices D s z hD hs t ks hk)

theorem indices_mem_allProfiles (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (t : List ℕ) (hlen : t.length ≤ SieveBoxLength.cutoff s)
    (hp : ∀ q ∈ t, q ∈ pool D s z) : indices D s t ∈ allProfiles s := by
  apply (mem_boundedTuples _ _ _).mpr
  refine ⟨by simpa only [indices, List.length_map] using hlen, ?_⟩
  intro j hj
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hj
  have hq' := (mem_pool D s z q).mp (hp q hq)
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le
    (boxIndex_le_cutoff D s q hD hs hq'.2.2 (hq'.2.1.trans_le hz)))

theorem outer_family_iff_profile (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (t : List ℕ) : t ∈ SieveUpperBoxing.outerFamily D s z ↔
      ∃ js ∈ outerProfiles s, Matches D s z t js := by
  rw [SieveUpperBoxing.mem_outerFamily D s z hD hs t]
  constructor
  · rintro ⟨hp, ha⟩
    refine ⟨indices D s t, Finset.mem_filter.mpr ⟨?_,
      (outerTest_iff_numeric D s hD t).mp ha⟩, matches_of_pool D s z hD hs hz t hp⟩
    exact indices_mem_allProfiles D s z hD hs hz t
      (SieveUpperBoxing.outerTest_length_bound D s hD hs t ha) hp
  · rintro ⟨js, hj, hm⟩
    have he := matches_indices D s z hD hs t js hm
    exact ⟨matches_pool D s z hD hs t js hm,
      (outerTest_iff_numeric D s hD t).mpr (he ▸ (Finset.mem_filter.mp hj).2)⟩

theorem inner_family_iff_profile (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (t : List ℕ) : t ∈ SieveUpperBoxing.innerFamily D s z ↔
      ∃ js ∈ innerProfiles s, Matches D s z t js := by
  rw [SieveUpperBoxing.mem_innerFamily D s z hD hs t]
  constructor
  · rintro ⟨hp, ha⟩
    refine ⟨indices D s t, Finset.mem_filter.mpr ⟨?_,
      (innerTest_iff_numeric D s hD t).mp ha⟩, matches_of_pool D s z hD hs hz t hp⟩
    exact indices_mem_allProfiles D s z hD hs hz t
      (SieveUpperBoxing.innerTest_length_bound D s hD hs t ha) hp
  · rintro ⟨js, hj, hm⟩
    have he := matches_indices D s z hD hs t js hm
    exact ⟨matches_pool D s z hD hs t js hm,
      (innerTest_iff_numeric D s hD t).mpr (he ▸ (Finset.mem_filter.mp hj).2)⟩

theorem outer_fixed_profile_iff (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (t js : List ℕ) :
    t ∈ SieveUpperBoxing.outerFamily D s z ∧ indices D s t = js ↔
      js ∈ outerProfiles s ∧ Matches D s z t js := by
  constructor
  · rintro ⟨ht, he⟩
    obtain ⟨ks, hk, hm⟩ := (outer_family_iff_profile D s z hD hs hz t).mp ht
    have hks : ks = js := (matches_indices D s z hD hs t ks hm).symm.trans he
    simpa only [hks] using And.intro hk hm
  · rintro ⟨hj, hm⟩
    exact ⟨(outer_family_iff_profile D s z hD hs hz t).mpr ⟨js, hj, hm⟩,
      matches_indices D s z hD hs t js hm⟩

theorem inner_fixed_profile_iff (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (t js : List ℕ) :
    t ∈ SieveUpperBoxing.innerFamily D s z ∧ indices D s t = js ↔
      js ∈ innerProfiles s ∧ Matches D s z t js := by
  constructor
  · rintro ⟨ht, he⟩
    obtain ⟨ks, hk, hm⟩ := (inner_family_iff_profile D s z hD hs hz t).mp ht
    have hks : ks = js := (matches_indices D s z hD hs t ks hm).symm.trans he
    simpa only [hks] using And.intro hk hm
  · rintro ⟨hj, hm⟩
    exact ⟨(inner_family_iff_profile D s z hD hs hz t).mpr ⟨js, hj, hm⟩,
      matches_indices D s z hD hs t js hm⟩

/-- Summing over fixed profiles is an exact partition of the original
ordered tuple sum. Distinct ordered tuples with the same product survive. -/
theorem outer_sum_profiles (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (f : List ℕ → ℂ) :
    (∑ t ∈ SieveUpperBoxing.outerFamily D s z, f t) =
      ∑ js ∈ outerProfiles s,
        ∑ t ∈ (SieveUpperBoxing.outerFamily D s z).filter (fun t => indices D s t = js), f t := by
  symm
  apply Finset.sum_fiberwise_of_maps_to
  intro t ht
  exact ((outer_fixed_profile_iff D s z hD hs hz t (indices D s t)).mp ⟨ht, rfl⟩).1

theorem inner_sum_profiles (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (f : List ℕ → ℂ) :
    (∑ t ∈ SieveUpperBoxing.innerFamily D s z, f t) =
      ∑ js ∈ innerProfiles s,
        ∑ t ∈ (SieveUpperBoxing.innerFamily D s z).filter (fun t => indices D s t = js), f t := by
  symm
  apply Finset.sum_fiberwise_of_maps_to
  intro t ht
  exact ((inner_fixed_profile_iff D s z hD hs hz t (indices D s t)).mp ⟨ht, rfl⟩).1

/-- With the other entries fixed, only the distinguished prime's literal
pool and box tests remain. No actual-prime ordering is introduced. -/
theorem matches_insert_iff (D s z : ℝ) (left right jleft jright : List ℕ) (q j : ℕ)
    (hl : Matches D s z left jleft) (hr : Matches D s z right jright) :
    Matches D s z (left ++ q :: right) (jleft ++ j :: jright) ↔
      q.Prime ∧ InBox D s (q : ℝ) j ∧ (q : ℝ) < z := by
  constructor
  · intro hm
    have hd := List.forall₂_drop_append (left ++ q :: right) jleft (j :: jright) hm
    rw [←hl.length_eq, List.drop_left] at hd
    exact (List.forall₂_cons.mp hd).1
  · intro hq
    exact List.rel_append hl (List.Forall₂.cons hq hr)

/-- Clamping is essential: a pool cutoff may lie below the box's lower end. -/
def truncatedHi (D s z : ℝ) (j : ℕ) : ℕ :=
  max (gridLo D s j) (strictEndpoint (min (scale D s (j + 1)) z))

theorem halfOpen_clamped_iff (A B : ℝ) (q : ℕ) (hA : 0 < A) (hB : 0 < B) :
    A ≤ (q : ℝ) ∧ (q : ℝ) < B ↔
      strictEndpoint A < q ∧ q ≤ max (strictEndpoint A) (strictEndpoint B) := by
  have hlo := lt_iff_le_strictEndpoint A q hA
  have hhi := lt_iff_le_strictEndpoint B q hB
  constructor
  · rintro ⟨hl, hh⟩
    exact ⟨lt_of_not_ge (fun h => (not_lt_of_ge hl) (hlo.mpr h)),
      (hhi.mp hh).trans (le_max_right _ _)⟩
  · rintro ⟨hl, hh⟩
    refine ⟨le_of_not_gt (fun h => (not_le_of_gt hl) (hlo.mp h)), hhi.mpr ?_⟩
    rcases le_max_iff.mp hh with hh | hh
    · exact False.elim ((not_le_of_gt hl) hh)
    · exact hh

theorem halfOpen_clamped_prefix (A B : ℝ) (q : ℕ) (hA : 0 < A) (hB : 0 < B) :
    (if A ≤ (q : ℝ) ∧ (q : ℝ) < B then (1 : ℂ) else 0) =
      prefixIndicator (max (strictEndpoint A) (strictEndpoint B)) q -
        prefixIndicator (strictEndpoint A) q := by
  simp only [halfOpen_clamped_iff A B q hA hB]
  unfold prefixIndicator
  by_cases hl : q ≤ strictEndpoint A
  · have hh : q ≤ max (strictEndpoint A) (strictEndpoint B) := hl.trans (le_max_left _ _)
    simp [hl, hh, not_lt_of_ge hl]
  · simp [hl, lt_of_not_ge hl]

theorem box_pool_iff_endpoints (D s z : ℝ) (j q : ℕ) (hD : 0 < D) (hz : 0 < z) :
    InBox D s (q : ℝ) j ∧ (q : ℝ) < z ↔
      gridLo D s j < q ∧ q ≤ truncatedHi D s z j := by
  have hA : 0 < scale D s j := Real.rpow_pos_of_pos hD _
  have hB : 0 < min (scale D s (j+1)) z := lt_min (Real.rpow_pos_of_pos hD _) hz
  simpa only [InBox, lt_min_iff, and_assoc, gridLo, truncatedHi] using
    halfOpen_clamped_iff (scale D s j) (min (scale D s (j+1)) z) q hA hB

theorem box_pool_prefix (D s z : ℝ) (j q : ℕ) (hD : 0 < D) (hz : 0 < z) :
    (if InBox D s (q : ℝ) j ∧ (q : ℝ) < z then (1 : ℂ) else 0) =
      prefixIndicator (truncatedHi D s z j) q - prefixIndicator (gridLo D s j) q := by
  have hA : 0 < scale D s j := Real.rpow_pos_of_pos hD _
  have hB : 0 < min (scale D s (j+1)) z := lt_min (Real.rpow_pos_of_pos hD _) hz
  simpa only [InBox, lt_min_iff, and_assoc, gridLo, truncatedHi] using
    halfOpen_clamped_prefix (scale D s j) (min (scale D s (j+1)) z) q hA hB

theorem truncatedHi_eq_lo_of_empty (D s z : ℝ) (j : ℕ) (hz : z ≤ scale D s j) :
    truncatedHi D s z j = gridLo D s j := by
  exact max_eq_left (strictEndpoint_mono _ _ ((min_le_right _ _).trans hz))

theorem box_pool_high_prefix (X D s z : ℝ) (j m q : ℕ)
    (hX : 0 ≤ X) (hD : 0 < D) (hz : 0 < z) (hm : 0 < m) :
    (if InBox D s (q : ℝ) j ∧ (q : ℝ) < z ∧ X ^ (109/200 : ℝ) < ((m*q : ℕ) : ℝ)
      then (1 : ℂ) else 0) =
      (prefixIndicator (truncatedHi D s z j) q - prefixIndicator (gridLo D s j) q) *
        (1 - prefixIndicator (physicalCut X m) q) := by
  rw [←box_pool_prefix D s z j q hD hz, ←physicalHigh_prefix X m q hX hm]
  simp only [←and_assoc]
  by_cases hb : InBox D s (q : ℝ) j ∧ (q : ℝ) < z <;>
    by_cases hh : X ^ (109/200 : ℝ) < ((m*q : ℕ) : ℝ) <;> simp_all only
  all_goals norm_num

theorem box_pool_high_expansion (X D s z : ℝ) (j m q Q : ℕ)
    (hX : 0 ≤ X) (hD : 0 < D) (hz : 0 < z) (hm : 0 < m) (hq : q ≤ Q) :
    (if InBox D s (q : ℝ) j ∧ (q : ℝ) < z ∧ X ^ (109/200 : ℝ) < ((m*q : ℕ) : ℝ)
      then (1 : ℂ) else 0) =
      ∑ a : Mode Q, scalar Q a * leftPhase Q a (gridLo D s j) (truncatedHi D s z j) *
        highPhase Q a (physicalCut X m) * rightPhase Q a q := by
  rw [box_pool_high_prefix X D s z j m q hX hD hz hm]
  exact separation Q (gridLo D s j) (truncatedHi D s z j) (physicalCut X m) q hq

theorem inserted_profile_high_expansion (X D s z : ℝ)
    (left right jleft jright : List ℕ) (j m q Q : ℕ)
    (hl : Matches D s z left jleft) (hr : Matches D s z right jright)
    (hX : 0 ≤ X) (hD : 0 < D) (hz : 0 < z) (hm : 0 < m) (hqp : q.Prime) (hq : q ≤ Q) :
    (if Matches D s z (left ++ q :: right) (jleft ++ j :: jright) ∧
      X ^ (109/200 : ℝ) < ((m*q : ℕ) : ℝ) then (1 : ℂ) else 0) =
      ∑ a : Mode Q, scalar Q a * leftPhase Q a (gridLo D s j) (truncatedHi D s z j) *
        highPhase Q a (physicalCut X m) * rightPhase Q a q := by
  simp only [matches_insert_iff D s z left right jleft jright q j hl hr,
    hqp, true_and, and_assoc]
  exact box_pool_high_expansion X D s z j m q Q hX hD hz hm hq

run_cmd do
  for decl in [``accepts_rpow_iff, ``scales_eq_profile, ``outerTest_iff_numeric,
      ``innerTest_iff_numeric, ``matches_indices, ``matches_pool, ``matches_of_pool,
      ``matches_iff, ``matches_unique, ``indices_mem_allProfiles,
      ``outer_family_iff_profile, ``inner_family_iff_profile,
      ``outer_fixed_profile_iff, ``inner_fixed_profile_iff, ``outer_sum_profiles,
      ``inner_sum_profiles, ``matches_insert_iff, ``halfOpen_clamped_iff,
      ``halfOpen_clamped_prefix, ``box_pool_iff_endpoints, ``box_pool_prefix,
      ``truncatedHi_eq_lo_of_empty, ``box_pool_high_prefix, ``box_pool_high_expansion,
      ``inserted_profile_high_expansion] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXACT FIXED UPPER TUPLE PROFILES AND CLAMPED POOL MASKS PASSED"

end LongerTupleProfile
