import SieveBoundaryReference

/-! Exact identification of the finite boundary reference with the actual
lower Rosser selector on the large-prime pool, restricted to distinct bands.
The length cutoff is discharged from the accepted cubic gates. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SieveReferenceSelector
open SieveBoxTuples SieveBoxedFamily SieveBoundaryReference SieveSignedComparison
open SieveStoppingExpansion

def selectedPart (positive : Bool) (D s z : ℝ) : Finset (Finset ℕ) :=
  if positive then evenPart (SieveRosser.selected D false (primes D s z))
  else oddPart (SieveRosser.selected D false (primes D s z))

def strictSelected (positive : Bool) (D s z : ℝ) : Finset (Finset ℕ) :=
  (selectedPart positive D s z).filter (fun A => (indices D s (descending A)).Nodup)

def selectedDistinct (D s z : ℝ) : Finset (Finset ℕ) :=
  (SieveRosser.selected D false (primes D s z)).filter
    (fun A => (indices D s (descending A)).Nodup)

def selectedReciprocal (positive : Bool) (D s z : ℝ) : ℝ :=
  ∑ A ∈ strictSelected positive D s z, (SievePrimeSubset.subsetProduct A : ℝ)⁻¹

theorem mem_selectedPart (positive : Bool) (D s z : ℝ) (A : Finset ℕ) :
    A ∈ selectedPart positive D s z ↔
      A ∈ SieveRosser.selected D false (primes D s z) ∧
        (if positive then Even A.card else ¬Even A.card) := by
  cases positive <;> simp only [selectedPart, Bool.false_eq_true, ite_false,
    ite_true, evenPart, oddPart, Finset.mem_filter]

theorem selected_subset_pool (D s z : ℝ) (A : Finset ℕ)
    (hA : A ∈ SieveRosser.selected D false (primes D s z)) : A ⊆ pool D s z := by
  simpa only [primes, descending_toFinset] using
    SieveRosser.selected_subset D false (primes D s z) A hA

/-- The actual selected subset satisfies the literal cutoff; it is not an
extra hypothesis on the reference family. -/
theorem selected_card_bound (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (A : Finset ℕ) (hA : A ∈ SieveRosser.selected D false (primes D s z)) :
    A.card ≤ SieveBoxLength.cutoff s := by
  apply SieveBoxLength.selected_card_le_cutoff D s (primes D s z) A hD hs ?_ hA
  intro p hp
  exact ((mem_pool D s z p).mp ((mem_descending _ p).mp hp)).2.2

theorem descending_mem_reference (positive : Bool) (D s z : ℝ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) (A : Finset ℕ)
    (hA : A ∈ strictSelected positive D s z) :
    descending A ∈ reference positive D s z := by
  obtain ⟨hpart, hidx⟩ := Finset.mem_filter.mp hA
  obtain ⟨hsel, hpar⟩ := (mem_selectedPart positive D s z A).mp hpart
  have hp : ∀ p ∈ descending A, p ∈ pool D s z :=
    fun p hm => selected_subset_pool D s z A hsel ((mem_descending A p).mp hm)
  have hw : (indices D s (descending A)).Pairwise (· ≥ ·) :=
    descending_box_indices D s hD hs (descending A) (descending_pairwise A)
      (range_of_pool D s z hz _ hp)
  apply (mem_reference positive D s z _).mpr
  refine ⟨?_, hp, ?_, (hw.and hidx).imp (fun h => by omega), ?_⟩
  · simpa only [descending_length] using selected_card_bound D s z hD hs A hsel
  · simpa only [descending_length] using hpar
  · exact descending_selected_accepts (SieveRosser.cubicGate D) false 1
      (primes D s z) (descending_nodup _) (descending_pairwise _) A hsel

theorem toFinset_mem_strictSelected (positive : Bool) (D s z : ℝ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) (t : List ℕ)
    (ht : t ∈ reference positive D s z) :
    t.toFinset ∈ strictSelected positive D s z := by
  have hstrict := reference_strict positive D s z hD hs hz t ht
  have hnodup : t.Nodup := hstrict.imp (fun h => ne_of_gt h)
  have hdesc := descending_eq_of_sorted t hnodup (hstrict.imp (fun h => h.le))
  obtain ⟨_, hp, hpar, hidx, ha⟩ := (mem_reference positive D s z t).mp ht
  have hsub : t.toFinset ⊆ (primes D s z).toFinset := by
    rw [primes, descending_toFinset]
    intro p hm
    exact hp p (List.mem_toFinset.mp hm)
  have hlist : t.Sublist (primes D s z) := by
    rw [← hdesc]
    exact descending_sublist t.toFinset (primes D s z)
      (descending_nodup _) (descending_pairwise _) hsub
  apply Finset.mem_filter.mpr
  refine ⟨(mem_selectedPart positive D s z t.toFinset).mpr ⟨?_, ?_⟩, ?_⟩
  · exact SievePrefix.selected_of_sublist_accepts (SieveRosser.cubicGate D) false 1
      (primes D s z) t hlist ha
  · simpa only [List.toFinset_card_of_nodup hnodup] using hpar
  · rw [hdesc]
    exact hidx.imp (fun h => ne_of_gt h)

/-- No tuple and no accepted subset is omitted by the finite length cap. -/
theorem reference_eq_image (positive : Bool) (D s z : ℝ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) :
    reference positive D s z = (strictSelected positive D s z).image descending := by
  ext t
  constructor
  · intro ht
    have ho := reference_strict positive D s z hD hs hz t ht
    exact Finset.mem_image.mpr ⟨t.toFinset,
      toFinset_mem_strictSelected positive D s z hD hs hz t ht,
      descending_eq_of_sorted t (ho.imp (fun h => ne_of_gt h)) (ho.imp (fun h => h.le))⟩
  · intro ht
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp ht
    exact descending_mem_reference positive D s z hD hs hz A hA

theorem tupleMass_reference_eq (positive : Bool) (D s z : ℝ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) :
    tupleMass (reference positive D s z) = selectedReciprocal positive D s z := by
  rw [reference_eq_image positive D s z hD hs hz]
  unfold tupleMass selectedReciprocal
  rw [sum_descending_kernel]
  simp only [SieveBoxMass.reciprocal, descending_prod]

theorem referenceDistinct_eq_selectedReciprocal (D s z : ℝ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) :
    referenceDistinct D s z = primeEuler (D^(s^2)) *
      (selectedReciprocal true D s z - selectedReciprocal false D s z) := by
  unfold referenceDistinct refEven refOdd
  rw [tupleMass_reference_eq true D s z hD hs hz,
    tupleMass_reference_eq false D s z hD hs hz]

theorem signed_reciprocal_sum (D s z : ℝ) :
    (∑ A ∈ selectedDistinct D s z,
      (-1 : ℝ)^A.card * (SievePrimeSubset.subsetProduct A : ℝ)⁻¹) =
      selectedReciprocal true D s z - selectedReciprocal false D s z := by
  unfold selectedDistinct selectedReciprocal strictSelected selectedPart evenPart oddPart
  simp only [ite_true, Bool.false_eq_true, ite_false, Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro A _
  rw [neg_one_pow_eq_ite]
  split_ifs <;> ring

/-- Euler-scaled reciprocal sum of the actual selected subsets, with only
the explicit distinct-index filter; neither f/F nor positivity is asserted. -/
theorem referenceDistinct_eq_signed_selected_sum (D s z : ℝ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) :
    referenceDistinct D s z = primeEuler (D^(s^2)) *
      ∑ A ∈ (SieveRosser.selected D false (primes D s z)).filter
        (fun A => (indices D s (descending A)).Nodup),
        (-1 : ℝ)^A.card * (SievePrimeSubset.subsetProduct A : ℝ)⁻¹ := by
  rw [referenceDistinct_eq_selectedReciprocal D s z hD hs hz,
    ← signed_reciprocal_sum D s z]
  rfl

run_cmd do
  for decl in [``mem_selectedPart, ``selected_subset_pool, ``selected_card_bound,
    ``descending_mem_reference, ``toFinset_mem_strictSelected, ``reference_eq_image,
    ``tupleMass_reference_eq, ``referenceDistinct_eq_selectedReciprocal,
    ``signed_reciprocal_sum, ``referenceDistinct_eq_signed_selected_sum] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "REFERENCE IDENTIFIED WITH ACTUAL SELECTED SUBSETS; LENGTH CUTOFF DISCHARGED"

end SieveReferenceSelector
end
