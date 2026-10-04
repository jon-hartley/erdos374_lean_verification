import SieveUpperModelLoss
import SieveUpperBoundaryReference
import SieveBoxMassRefined
import SieveProfileCollision

/-! Actual repeated-band mass in the positive outer upper family. Grouping
preserves every Cartesian representation; no unit coefficient bound is used. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators
namespace SieveUpperOuterCollisions
open SieveBoxMass SieveStoppingExpansion
open SieveBoxedFamily (pool indices)
open SieveUpperModelLoss (outerMass innerMass)
open SieveUpperBoundaryReference (tupleMass outerDistinct strictIdeal)

def collisions (D s z : ℝ) : Finset (List ℕ) :=
  (SieveUpperBoxing.outerFamily D s z).filter (fun t => ¬(indices D s t).Nodup)
def collisionMass (D s z : ℝ) : ℝ := ∑ t ∈ collisions D s z, reciprocal t

theorem collisionMass_nonneg (D s z : ℝ) : 0 ≤ collisionMass D s z :=
  Finset.sum_nonneg (fun t _ => inv_nonneg.mpr (Nat.cast_nonneg t.prod))

theorem outerMass_sub_distinctMass (D s z : ℝ) :
    outerMass D s z-tupleMass (outerDistinct D s z) = collisionMass D s z := by
  classical
  have h := Finset.sum_filter_add_sum_filter_not (SieveUpperBoxing.outerFamily D s z)
    (fun t => (indices D s t).Nodup) reciprocal
  have he : (∑ t ∈ SieveUpperBoxing.outerFamily D s z, reciprocal t) = outerMass D s z := by
    simp only [outerMass, reciprocal, one_div]
  rw [he] at h
  change tupleMass (outerDistinct D s z)+collisionMass D s z=outerMass D s z at h
  linarith

theorem ideal_sub_strictIdeal (D s z : ℝ) :
    SieveUpperModelLoss.ideal D s z-strictIdeal D s z =
      primeEuler (D^(s^2))*collisionMass D s z := by
  have hi : innerMass D s z=tupleMass (SieveUpperBoxing.innerFamily D s z) := by
    simp only [innerMass, tupleMass, reciprocal, one_div]
  change primeEuler (D^(s^2))*(outerMass D s z-innerMass D s z)-
    primeEuler (D^(s^2))*(tupleMass (outerDistinct D s z)-
      tupleMass (SieveUpperBoxing.innerFamily D s z)) = _
  rw [hi]
  rw [show primeEuler (D^(s^2))*(outerMass D s z-tupleMass (SieveUpperBoxing.innerFamily D s z))-
      primeEuler (D^(s^2))*(tupleMass (outerDistinct D s z)-tupleMass (SieveUpperBoxing.innerFamily D s z)) =
      primeEuler (D^(s^2))*(outerMass D s z-tupleMass (outerDistinct D s z)) by ring,
    outerMass_sub_distinctMass]

theorem mainTerm_strict_exact (D s z : ℝ) :
    SieveUpperBoxWindow.mainTerm D s z = strictIdeal D s z+
      primeEuler (D^(s^2))*collisionMass D s z+SieveUpperModelLoss.excess D s z := by
  have h := ideal_sub_strictIdeal D s z
  unfold SieveUpperModelLoss.excess
  linarith

/-- Arbitrary actual tuple families with repeated sorted indices are bounded
by full Cartesian fibre masses, then by the generic repeated-profile sum. -/
theorem repeated_indices_mass_le (D s z η : ℝ) (A : Finset (List ℕ)) (K : ℕ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (hlen : ∀ t ∈ A, t.length ≤ K)
    (hpool : ∀ t ∈ A, ∀ p ∈ t, p ∈ pool D s z)
    (hsorted : ∀ t ∈ A, (indices D s t).Pairwise (· ≥ ·))
    (hrep : ∀ t ∈ A, ¬(indices D s t).Nodup)
    (hband : ∀ i ≤ SieveGeometricGrid.cutoff s, bandMass D s z i ≤ 1/17)
    (hη : ∀ i ≤ SieveGeometricGrid.cutoff s, bandMass D s z i ≤ η) :
    (∑ t ∈ A, reciprocal t) ≤
      (η*primeMass D s z)*Real.exp ((17/16)*primeMass D s z) := by
  classical
  let G := A.image (indices D s)
  have hmaps : ∀ t ∈ A, indices D s t ∈ G := fun t ht => Finset.mem_image.mpr ⟨t, ht, rfl⟩
  have hsum : (∑ t ∈ A, reciprocal t) =
      ∑ g ∈ G, ∑ t ∈ A.filter (fun t => indices D s t = g), reciprocal t :=
    (Finset.sum_fiberwise_of_maps_to hmaps reciprocal).symm
  have hfibre : (∑ t ∈ A, reciprocal t) ≤ ∑ g ∈ G, (g.map (bandMass D s z)).prod := by
    rw [hsum]
    apply Finset.sum_le_sum
    intro g hg
    rw [← fibre_mass D s z g]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro t ht
      obtain ⟨htA, he⟩ := Finset.mem_filter.mp ht
      exact (SieveBoxGrouping.mem_fibre_iff_indices D s z hD hs hz g t).mpr ⟨hpool t htA, he⟩
    · intro t _ _
      exact inv_nonneg.mpr (Nat.cast_nonneg t.prod)
  have hdata : ∀ g ∈ G, g.length ≤ K ∧
      (∀ i ∈ g, i < SieveGeometricGrid.cutoff s+1) ∧ g.Pairwise (· ≥ ·) ∧ ¬g.Nodup := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hg
    refine ⟨by simpa only [indices, List.length_map] using hlen t ht, ?_, hsorted t ht, hrep t ht⟩
    intro i hi
    exact Nat.lt_succ_of_le
      (SieveCompleteBoxing.assigned_indices_bounded D s z hD hs hz t (hpool t ht) i hi)
  have hp := SieveProfileCollision.repeated_mass_le_product G (SieveGeometricGrid.cutoff s+1)
    K (bandMass D s z) (fun g hg => (hdata g hg).1)
    (fun g hg => (hdata g hg).2.1) (fun g hg => (hdata g hg).2.2.1)
    (fun g hg => (hdata g hg).2.2.2) (fun i _ => bandMass_nonneg D s z i)
    (fun i hi => (hband i (Nat.lt_succ_iff.mp hi)).trans_lt (by norm_num))
  have he := SieveProfileMass.product_inverse_le_exp_sharp (SieveGeometricGrid.cutoff s+1)
    (bandMass D s z) (fun i _ => bandMass_nonneg D s z i)
    (fun i hi => hband i (Nat.lt_succ_iff.mp hi))
  have hsq : (∑ i ∈ Finset.range (SieveGeometricGrid.cutoff s+1), bandMass D s z i^2) ≤
      η*primeMass D s z := by
    rw [← sum_bandMass D s z hD hs hz, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right (hη i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
      (bandMass_nonneg D s z i)
  rw [sum_bandMass D s z hD hs hz] at he
  exact hfibre.trans (hp.trans ((mul_le_mul_of_nonneg_left he
    (Finset.sum_nonneg (fun i _ => sq_nonneg _))).trans
      (mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le)))

theorem collisionMass_le (D s z η : ℝ) (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (hband : ∀ i ≤ SieveGeometricGrid.cutoff s, bandMass D s z i ≤ 1/17)
    (hη : ∀ i ≤ SieveGeometricGrid.cutoff s, bandMass D s z i ≤ η) :
    collisionMass D s z ≤ (η*primeMass D s z)*Real.exp ((17/16)*primeMass D s z) := by
  classical
  apply repeated_indices_mass_le D s z η (collisions D s z) (SieveBoxLength.cutoff s) hD hs hz
  · intro t ht
    exact ((SieveBoxedFamily.mem_boundedTuples _ _ _).mp
      (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1).1
  · intro t ht
    exact ((SieveUpperBoxing.mem_outerFamily D s z hD hs t).mp (Finset.mem_filter.mp ht).1).1
  · intro t ht
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2.2.1
  · intro t ht
    exact (Finset.mem_filter.mp ht).2
  · exact hband
  · exact hη

run_cmd do
  for decl in [``collisionMass_nonneg, ``outerMass_sub_distinctMass,
      ``ideal_sub_strictIdeal, ``mainTerm_strict_exact, ``repeated_indices_mass_le,
      ``collisionMass_le] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL OUTER UPPER COLLISIONS; ALL CARTESIAN MULTIPLICITIES RETAINED"
end SieveUpperOuterCollisions
end
