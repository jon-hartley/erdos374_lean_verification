import SieveUpperModelLoss
import SieveBoxMassTwo
import SieveStoppingBudget

/-! Unsigned reciprocal mass of the actual upper box families. Grouping by
the assigned index list preserves every repeated outer coordinate. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators
namespace SieveUpperBoxMass
open SieveBoxMass SieveBoxedFamily SieveUpperModelLoss

/-- A finite family with weakly decreasing assigned indices is bounded by
the complete Cartesian fibres; no tuple injectivity into profiles is assumed. -/
theorem sorted_indices_mass_le_exp (D s z : ℝ) (A : Finset (List ℕ)) (K : ℕ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (hlen : ∀ t ∈ A, t.length ≤ K)
    (hpool : ∀ t ∈ A, ∀ p ∈ t, p ∈ pool D s z)
    (hsorted : ∀ t ∈ A, (indices D s t).Pairwise (· ≥ ·))
    (hband : ∀ i ≤ SieveGeometricGrid.cutoff s, bandMass D s z i ≤ 1/2) :
    (∑ t ∈ A, reciprocal t) ≤ Real.exp (2*primeMass D s z) := by
  classical
  let G := A.image (indices D s)
  have hmaps : ∀ t ∈ A, indices D s t ∈ G := fun t ht => Finset.mem_image.mpr ⟨t, ht, rfl⟩
  have hsum : (∑ t ∈ A, reciprocal t) =
      ∑ g ∈ G, ∑ t ∈ A.filter (fun t => indices D s t = g), reciprocal t :=
    (Finset.sum_fiberwise_of_maps_to hmaps reciprocal).symm
  have hfibre : (∑ t ∈ A, reciprocal t) ≤
      ∑ g ∈ G, (g.map (bandMass D s z)).prod := by
    rw [hsum]
    apply Finset.sum_le_sum
    intro g hg
    rw [← SieveBoxMass.fibre_mass D s z g]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro t ht
      obtain ⟨htA, he⟩ := Finset.mem_filter.mp ht
      exact (SieveBoxGrouping.mem_fibre_iff_indices D s z hD hs hz g t).mpr
        ⟨hpool t htA, he⟩
    · intro t _ _
      exact inv_nonneg.mpr (Nat.cast_nonneg t.prod)
  have hdata : ∀ g ∈ G, g.length ≤ K ∧
      (∀ i ∈ g, i < SieveGeometricGrid.cutoff s+1) ∧ g.Pairwise (· ≥ ·) := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hg
    refine ⟨by simpa only [indices, List.length_map] using hlen t ht, ?_, hsorted t ht⟩
    intro i hi
    exact Nat.lt_succ_of_le (SieveCompleteBoxing.assigned_indices_bounded D s z hD hs hz t (hpool t ht) i hi)
  have hbound := SieveProfileMass.sorted_mass_le_exp G (SieveGeometricGrid.cutoff s+1)
    K (bandMass D s z) (fun g hg => (hdata g hg).1)
    (fun g hg => (hdata g hg).2.1) (fun g hg => (hdata g hg).2.2)
    (fun i _ => bandMass_nonneg D s z i)
    (fun i hi => hband i (Nat.lt_succ_iff.mp hi))
  exact hfibre.trans (by simpa only [sum_bandMass D s z hD hs hz] using hbound)

theorem families_disjoint (D s z : ℝ) :
    Disjoint (SieveUpperBoxing.outerFamily D s z) (SieveUpperBoxing.innerFamily D s z) := by
  classical
  apply Finset.disjoint_left.mpr
  intro t ho hi
  have he := (Finset.mem_filter.mp ho).2.1
  have hn := (Finset.mem_filter.mp hi).2.1
  exact hn he

theorem total_mass_le_exp_of_band_bound (D s z : ℝ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (hband : ∀ i ≤ SieveGeometricGrid.cutoff s, bandMass D s z i ≤ 1/2) :
    outerMass D s z+innerMass D s z ≤ Real.exp (2*primeMass D s z) := by
  classical
  have hdata : ∀ t ∈ SieveUpperBoxing.outerFamily D s z ∪ SieveUpperBoxing.innerFamily D s z,
      t.length ≤ SieveBoxLength.cutoff s ∧ (∀ p ∈ t, p ∈ pool D s z) ∧
        (indices D s t).Pairwise (· ≥ ·) := by
    intro t ht
    rcases Finset.mem_union.mp ht with ho | hi
    · obtain ⟨hp, htest⟩ := (SieveUpperBoxing.mem_outerFamily D s z hD hs t).mp ho
      exact ⟨SieveUpperBoxing.outerTest_length_bound D s hD hs t htest, hp, htest.2.1⟩
    · obtain ⟨hp, htest⟩ := (SieveUpperBoxing.mem_innerFamily D s z hD hs t).mp hi
      exact ⟨SieveUpperBoxing.innerTest_length_bound D s hD hs t htest, hp,
        htest.2.1.imp (fun h => h.le)⟩
  have hh := sorted_indices_mass_le_exp D s z _ (SieveBoxLength.cutoff s) hD hs hz
    (fun t ht => (hdata t ht).1) (fun t ht => (hdata t ht).2.1)
    (fun t ht => (hdata t ht).2.2) hband
  rw [Finset.sum_union (families_disjoint D s z)] at hh
  simpa only [outerMass, innerMass, reciprocal, one_div] using hh

/-- One threshold precedes every actual upper cutoff. -/
theorem eventually_total_mass (s : ℝ) (hs : 0 < s) (hsHalf : s ≤ 1/2) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ, z ≤ D →
      outerMass D s z+innerMass D s z ≤ Real.exp 2*(1/s)^8 := by
  obtain ⟨D₀, hD₀, hb⟩ := SieveBoxMassTwo.small_parameter_bounds_two s hs hsHalf
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD z hz
  obtain ⟨_, hband, _, hprime, _⟩ := hb D hD z hz
  calc
    _ ≤ Real.exp (2*primeMass D s z) := total_mass_le_exp_of_band_bound D s z
      (hD₀.trans_le hD) hs hz (fun i _ => (hband i).trans (by norm_num))
    _ ≤ Real.exp (2*(2*Real.log (1/s^2)+1)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hprime (by norm_num))
    _ = _ := SieveStoppingBudget.profile_exp_identity s hs

run_cmd do
  for decl in [``sorted_indices_mass_le_exp, ``families_disjoint,
      ``total_mass_le_exp_of_band_bound, ``eventually_total_mass] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL UPPER FAMILIES: TOTAL RECIPROCAL MASS BOUNDED BY SORTED PROFILES"
end SieveUpperBoxMass
end
