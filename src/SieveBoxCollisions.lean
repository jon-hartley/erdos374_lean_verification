import SieveBoxMassRefined
import SieveProfileCollision

/-! Same-band errors for the actual complete Cartesian tuple families.
This removes weak-order repetitions only; cubic-boundary discrepancies remain. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators
namespace SieveBoxCollisions
open SieveBoxGrouping SieveBoxedFamily SieveBoxMass SieveGeometricGrid

def collisionMass (positive : Bool) (D s z : ℝ) : ℝ :=
  ∑ t ∈ (family positive D s z).filter (fun t => ¬(indices D s t).Nodup), reciprocal t

def repeatedPrimeMass (positive : Bool) (D s z : ℝ) : ℝ :=
  ∑ t ∈ (family positive D s z).filter (fun t => ¬t.Nodup), reciprocal t

theorem collisionMass_nonneg (positive : Bool) (D s z : ℝ) :
    0 ≤ collisionMass positive D s z :=
  Finset.sum_nonneg (fun t _ => inv_nonneg.mpr (Nat.cast_nonneg t.prod))

theorem collisionMass_eq_profiles (positive : Bool) (D s z : ℝ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) :
    collisionMass positive D s z =
      ∑ g ∈ (profiles positive D s).filter (fun g => ¬g.Nodup),
        (g.map (bandMass D s z)).prod := by
  classical
  rw [collisionMass, Finset.sum_filter, sum_grouped positive D s z hD hs hz,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro g _
  calc
    _ = ∑ t ∈ fibre D s z g, if ¬g.Nodup then reciprocal t else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [((mem_fibre_iff_indices D s z hD hs hz g t).mp ht).2]
    _ = _ := by
      by_cases hg : g.Nodup <;> simp [hg, fibre_mass]

theorem inner_collisionMass_zero (D s z : ℝ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) : collisionMass true D s z = 0 := by
  classical
  rw [collisionMass_eq_profiles true D s z hD hs hz]
  apply Finset.sum_eq_zero
  intro g hg
  obtain ⟨hg, hn⟩ := Finset.mem_filter.mp hg
  have hstrict : g.Pairwise (· > ·) := ((mem_profiles true D s g).mp hg).2.2.2.1
  exact (hn (List.nodup_iff_pairwise_ne.mpr (hstrict.imp (fun h => ne_of_gt h)))).elim

theorem repeatedPrimeMass_le_collisionMass (positive : Bool) (D s z : ℝ) :
    repeatedPrimeMass positive D s z ≤ collisionMass positive D s z := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro t ht
    obtain ⟨ht, hn⟩ := Finset.mem_filter.mp ht
    refine Finset.mem_filter.mpr ⟨ht, fun hi => hn ?_⟩
    exact List.Nodup.of_map _ hi
  · intro t _ _
    exact inv_nonneg.mpr (Nat.cast_nonneg t.prod)

theorem collisionMass_le (positive : Bool) (D s z η : ℝ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (hband : ∀ i ≤ cutoff s, bandMass D s z i ≤ 1/17)
    (hη : ∀ i ≤ cutoff s, bandMass D s z i ≤ η) :
    collisionMass positive D s z ≤
      (η * primeMass D s z) * Real.exp ((17/16) * primeMass D s z) := by
  classical
  rw [collisionMass_eq_profiles positive D s z hD hs hz]
  have hp := SieveProfileCollision.repeated_mass_le_product
    ((profiles positive D s).filter (fun g => ¬g.Nodup))
    (cutoff s+1) (SieveBoxLength.cutoff s) (bandMass D s z)
    (fun g hg => ((mem_profiles positive D s g).mp (Finset.mem_filter.mp hg).1).1)
    (fun g hg i hi => Nat.lt_succ_of_le
      (((mem_profiles positive D s g).mp (Finset.mem_filter.mp hg).1).2.1 i hi))
    (fun g hg => profile_sorted positive D s g (Finset.mem_filter.mp hg).1)
    (fun _ hg => (Finset.mem_filter.mp hg).2)
    (fun i _ => bandMass_nonneg D s z i)
    (fun i hi => (hband i (Nat.lt_succ_iff.mp hi)).trans_lt (by norm_num))
  have he := SieveProfileMass.product_inverse_le_exp_sharp (cutoff s+1) (bandMass D s z)
    (fun i _ => bandMass_nonneg D s z i) (fun i hi => hband i (Nat.lt_succ_iff.mp hi))
  have hsq : (∑ i ∈ Finset.range (cutoff s+1), bandMass D s z i ^ 2) ≤
      η * primeMass D s z := by
    rw [← sum_bandMass D s z hD hs hz, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right (hη i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
      (bandMass_nonneg D s z i)
  rw [sum_bandMass D s z hD hs hz] at he
  exact hp.trans ((mul_le_mul_of_nonneg_left he
    (Finset.sum_nonneg (fun i _ => sq_nonneg _))).trans
      (mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le))

#print axioms collisionMass_le
run_cmd do
  for decl in [``collisionMass_nonneg, ``collisionMass_eq_profiles,
    ``inner_collisionMass_zero, ``repeatedPrimeMass_le_collisionMass, ``collisionMass_le] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end SieveBoxCollisions
end
