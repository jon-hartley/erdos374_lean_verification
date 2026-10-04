import SieveUpperReferenceSelector
import SieveFullCutoffTransfer

/-! Exact signed comparison of the unrestricted large-prime selector with
its distinct-band restriction. The lost even and odd signs are both retained. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open SieveBoxedFamily SieveBoxTuples SieveUpperBoundaryReference SieveStoppingExpansion

namespace SieveUpperPoolReference

def selected (D s z : ℝ) : Finset (Finset ℕ) :=
  SieveRosser.selected D true (primes D s z)

def colliding (D s z : ℝ) : Finset (Finset ℕ) :=
  (selected D s z).filter (fun A => ¬(indices D s (descending A)).Nodup)

def collisionTuples (D s z : ℝ) : Finset (List ℕ) := (colliding D s z).image descending

def collisionMass (D s z : ℝ) : ℝ :=
  ∑ A ∈ colliding D s z, (SievePrimeSubset.subsetProduct A : ℝ)⁻¹

def reference (D s z : ℝ) : ℝ :=
  primeEuler (D^(s^2))*∑ A ∈ selected D s z,
    (-1:ℝ)^A.card * (SievePrimeSubset.subsetProduct A : ℝ)⁻¹

theorem collisionMass_nonneg (D s z : ℝ) : 0 ≤ collisionMass D s z := by
  unfold collisionMass
  exact Finset.sum_nonneg (fun A _ => inv_nonneg.mpr (Nat.cast_nonneg _))

theorem collisionMass_eq_tupleMass (D s z : ℝ) :
    collisionMass D s z = tupleMass (collisionTuples D s z) := by
  unfold collisionMass tupleMass collisionTuples
  rw [sum_descending_kernel]
  simp only [SieveBoxMass.reciprocal, descending_prod]

theorem collisionTuples_properties (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (t : List ℕ) (ht : t ∈ collisionTuples D s z) :
    t.Pairwise (· > ·) ∧ (∀ p ∈ t, p ∈ pool D s z) ∧
      t.length ≤ SieveBoxLength.cutoff s ∧ ¬(indices D s t).Nodup := by
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨ha, hn⟩ := Finset.mem_filter.mp hA
  refine ⟨descending_strict A, ?_, ?_, hn⟩
  · intro p hp
    exact SieveUpperReferenceSelector.selected_subset_pool D s z A ha ((mem_descending A p).mp hp)
  · simpa only [descending_length] using
      SieveUpperReferenceSelector.selected_card_bound D s z hD hs A ha

theorem difference_exact (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) :
    reference D s z - referenceDistinct D s z =
      primeEuler (D^(s^2))*∑ A ∈ colliding D s z,
        (-1:ℝ)^A.card * (SievePrimeSubset.subsetProduct A : ℝ)⁻¹ := by
  rw [SieveUpperReferenceSelector.referenceDistinct_eq_signed_selected_sum D s z hD hs hz]
  have hh := Finset.sum_filter_add_sum_filter_not (selected D s z)
    (fun A => (indices D s (descending A)).Nodup)
    (fun A => (-1:ℝ)^A.card*(SievePrimeSubset.subsetProduct A : ℝ)⁻¹)
  unfold reference colliding
  change _ + _ = _ at hh
  change primeEuler (D^(s^2))*_ - primeEuler (D^(s^2))*_ = _
  rw [← hh]
  unfold selected
  ring

theorem difference_abs_le (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) :
    |reference D s z - referenceDistinct D s z| ≤
      primeEuler (D^(s^2))*collisionMass D s z := by
  rw [difference_exact D s z hD hs hz, abs_mul,
    abs_of_pos (SieveEulerRatio.euler_pos _)]
  apply mul_le_mul_of_nonneg_left _ (SieveEulerRatio.euler_pos _).le
  calc
    _ ≤ ∑ A ∈ colliding D s z,
        |(-1:ℝ)^A.card*(SievePrimeSubset.subsetProduct A : ℝ)⁻¹| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = collisionMass D s z := by
      unfold collisionMass
      apply Finset.sum_congr rfl
      intro A _
      rw [abs_mul, abs_pow]
      simp only [abs_neg, abs_one, one_pow, one_mul]
      exact abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem reference_eq_euler_mul_upperLarge (D s z : ℝ) :
    reference D s z = primeEuler (D^(s^2))*SieveFullCutoffTransfer.upperLarge D s z := by
  rw [SieveFullCutoffTransfer.upperLarge, SieveFullCutoffTransfer.value_eq_signed_reciprocal]
  rfl

run_cmd do
  for decl in [``collisionMass_nonneg, ``collisionMass_eq_tupleMass,
    ``collisionTuples_properties, ``difference_exact, ``difference_abs_le, ``reference_eq_euler_mul_upperLarge] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXACT SIGNED UPPER LARGE-POOL REFERENCE DIFFERENCE PASSED"
end SieveUpperPoolReference
end
