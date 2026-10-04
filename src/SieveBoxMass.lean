import SieveProfileMass

/-! Unsigned reciprocal mass of the actual complete box families.
The combinatorial bound is uniform in their admitted length. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators

namespace SieveBoxMass
open SieveBoxGrouping SieveBoxedFamily SieveGeometricGrid

def reciprocal (t : List ℕ) : ℝ := (t.prod : ℝ)⁻¹
def bandMass (D s z : ℝ) (i : ℕ) : ℝ := ∑ p ∈ primeBand D s z i, (p : ℝ)⁻¹
def primeMass (D s z : ℝ) : ℝ := ∑ p ∈ pool D s z, (p : ℝ)⁻¹
def mass (positive : Bool) (D s z : ℝ) : ℝ := ∑ t ∈ family positive D s z, reciprocal t

theorem bandMass_nonneg (D s z : ℝ) (i : ℕ) : 0 ≤ bandMass D s z i :=
  Finset.sum_nonneg (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p))

theorem mass_nonneg (positive : Bool) (D s z : ℝ) : 0 ≤ mass positive D s z :=
  Finset.sum_nonneg (fun t _ => inv_nonneg.mpr (Nat.cast_nonneg t.prod))

theorem reciprocal_cons (p : ℕ) (t : List ℕ) :
    reciprocal (p::t) = (p : ℝ)⁻¹ * reciprocal t := by
  simp only [reciprocal, List.prod_cons, Nat.cast_mul, mul_inv]

theorem fibre_mass (D s z : ℝ) (g : List ℕ) :
    (∑ t ∈ fibre D s z g, reciprocal t) = (g.map (bandMass D s z)).prod := by
  classical
  induction g with
  | nil => simp [fibre, reciprocal]
  | cons i g ih =>
    have hd : (↑(primeBand D s z i) : Set ℕ).PairwiseDisjoint
        (fun p => (fibre D s z g).image (List.cons p)) := by
      intro p _ q _ hpq
      apply Finset.disjoint_left.mpr
      intro t ht hq
      obtain ⟨v, _, hv⟩ := Finset.mem_image.mp ht
      obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hq
      exact hpq (List.cons.inj (hv.trans hw.symm)).1
    rw [fibre, Finset.sum_biUnion hd]
    calc
      _ = ∑ p ∈ primeBand D s z i, (p : ℝ)⁻¹ * ∑ t ∈ fibre D s z g, reciprocal t := by
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.sum_image]
        · simp only [reciprocal_cons, Finset.mul_sum]
        · intro v _ w _ he
          exact (List.cons.inj he).2
      _ = _ := by simp only [ih, ← Finset.sum_mul, List.map_cons, List.prod_cons, bandMass]

theorem mass_eq_profile_mass (positive : Bool) (D s z : ℝ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) :
    mass positive D s z = ∑ g ∈ profiles positive D s, (g.map (bandMass D s z)).prod := by
  rw [mass, sum_grouped positive D s z hD hs hz]
  exact Finset.sum_congr rfl (fun g _ => fibre_mass D s z g)

theorem sum_bandMass (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) :
    (∑ i ∈ Finset.range (cutoff s+1), bandMass D s z i) = primeMass D s z := by
  classical
  have he : ∀ i, primeBand D s z i = (pool D s z).filter
      (fun p : ℕ => SieveBoxTuples.boxIndex D s (p : ℝ) = i) := by
    intro i
    ext p
    simp only [mem_primeBand_iff_index D s z hD hs hz, Finset.mem_filter]
  have hm : ∀ p ∈ pool D s z, SieveBoxTuples.boxIndex D s (p : ℝ) ∈
      Finset.range (cutoff s+1) := by
    intro p hp
    have hh := (mem_pool D s z p).mp hp
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      (SieveBoxTuples.boxIndex_le_cutoff D s (p : ℝ) hD hs hh.2.2 (hh.2.1.trans_le hz)))
  unfold bandMass primeMass
  simp_rw [he]
  exact Finset.sum_fiberwise_of_maps_to hm (fun p : ℕ => (p : ℝ)⁻¹)

theorem profile_sorted (positive : Bool) (D s : ℝ) (g : List ℕ)
    (hg : g ∈ profiles positive D s) : g.Pairwise (· ≥ ·) := by
  have ht := ((mem_profiles positive D s g).mp hg).2.2
  cases positive with
  | false => exact ht.2.1
  | true => exact ht.2.1.imp (fun h => h.le)

/-- No exponential dependence on the sequence cutoff is incurred. -/
theorem mass_le_exp_of_band_bound (positive : Bool) (D s z : ℝ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (hband : ∀ i ≤ cutoff s, bandMass D s z i ≤ 1/2) :
    mass positive D s z ≤ Real.exp (2 * primeMass D s z) := by
  rw [mass_eq_profile_mass positive D s z hD hs hz]
  have h := SieveProfileMass.sorted_mass_le_exp (profiles positive D s)
    (cutoff s+1) (SieveBoxLength.cutoff s) (bandMass D s z)
    (fun g hg => ((mem_profiles positive D s g).mp hg).1)
    (fun g hg i hi => Nat.lt_succ_of_le (((mem_profiles positive D s g).mp hg).2.1 i hi))
    (profile_sorted positive D s) (fun i _ => bandMass_nonneg D s z i)
    (fun i hi => hband i (Nat.lt_succ_iff.mp hi))
  simpa only [sum_bandMass D s z hD hs hz] using h

theorem profiles_disjoint (D s : ℝ) : Disjoint (profiles true D s) (profiles false D s) := by
  classical
  apply Finset.disjoint_left.mpr
  intro g hi ho
  have hI := ((mem_profiles true D s g).mp hi).2.2
  have hO := ((mem_profiles false D s g).mp ho).2.2
  exact hO.1 hI.1

theorem total_mass_le_exp_of_band_bound (D s z : ℝ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (hband : ∀ i ≤ cutoff s, bandMass D s z i ≤ 1/2) :
    mass true D s z + mass false D s z ≤ Real.exp (2 * primeMass D s z) := by
  classical
  rw [mass_eq_profile_mass true D s z hD hs hz,
    mass_eq_profile_mass false D s z hD hs hz, ← Finset.sum_union (profiles_disjoint D s)]
  have hdata : ∀ g ∈ profiles true D s ∪ profiles false D s,
      g.length ≤ SieveBoxLength.cutoff s ∧ (∀ i ∈ g, i < cutoff s+1) ∧ g.Pairwise (· ≥ ·) := by
    intro g hg
    rcases Finset.mem_union.mp hg with hg | hg
    · have h := (mem_profiles true D s g).mp hg
      exact ⟨h.1, fun i hi => Nat.lt_succ_of_le (h.2.1 i hi), profile_sorted true D s g hg⟩
    · have h := (mem_profiles false D s g).mp hg
      exact ⟨h.1, fun i hi => Nat.lt_succ_of_le (h.2.1 i hi), profile_sorted false D s g hg⟩
  have h := SieveProfileMass.sorted_mass_le_exp _ (cutoff s+1) (SieveBoxLength.cutoff s)
    (bandMass D s z) (fun g hg => (hdata g hg).1)
    (fun g hg => (hdata g hg).2.1) (fun g hg => (hdata g hg).2.2)
    (fun i _ => bandMass_nonneg D s z i) (fun i hi => hband i (Nat.lt_succ_iff.mp hi))
  simpa only [sum_bandMass D s z hD hs hz] using h

#print axioms total_mass_le_exp_of_band_bound
run_cmd do
  for decl in [``bandMass_nonneg, ``mass_nonneg, ``reciprocal_cons, ``fibre_mass,
    ``mass_eq_profile_mass, ``sum_bandMass, ``profile_sorted,
    ``mass_le_exp_of_band_bound, ``profiles_disjoint, ``total_mass_le_exp_of_band_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end SieveBoxMass
end
