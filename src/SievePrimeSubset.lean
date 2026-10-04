import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

/-! Port of the checked finite constructor from HarmanPrimeSubset169.lean.
This module imports only Mathlib and does not import an old Erdos checkpoint.
Concrete collection of parity-signed selected prime subsets.  Selecting the
subsets by the source stopped sieve recursion remains a separate construction. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open scoped BigOperators
namespace SievePrimeSubset

def subsetProduct (s : Finset ℕ) : ℕ := ∏ p ∈ s, p

theorem prime_subset_product_injective (s t : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) (ht : ∀ p ∈ t, p.Prime)
    (he : subsetProduct s = subsetProduct t) : s = t := by
  have h := congrArg Nat.primeFactors he
  simpa only [subsetProduct, Nat.primeFactors_prod hs, Nat.primeFactors_prod ht] using h

/-- Actual collection by integer product; each selected subset contributes its parity sign. -/
def selectedCoefficient (A : Finset (Finset ℕ)) (m : ℕ) : ℝ :=
  ∑ s ∈ A.filter (fun s => subsetProduct s = m), (-1 : ℝ)^s.card

theorem selectedCoefficient_eq_sign (A : Finset (Finset ℕ))
    (hA : ∀ s ∈ A, ∀ p ∈ s, p.Prime) (s : Finset ℕ) (hs : s ∈ A) :
    selectedCoefficient A (subsetProduct s) = (-1 : ℝ)^s.card := by
  unfold selectedCoefficient
  have hsF : s ∈ A.filter (fun t => subsetProduct t = subsetProduct s) :=
    Finset.mem_filter.mpr ⟨hs, rfl⟩
  apply Finset.sum_eq_single_of_mem s hsF
  intro t ht hts
  obtain ⟨htA, he⟩ := Finset.mem_filter.mp ht
  exact (hts (prime_subset_product_injective t s (hA t htA) (hA s hs) he)).elim

theorem selectedCoefficient_eq_zero (A : Finset (Finset ℕ)) (m : ℕ)
    (h : ∀ s ∈ A, subsetProduct s ≠ m) : selectedCoefficient A m = 0 := by
  unfold selectedCoefficient
  have he : A.filter (fun s => subsetProduct s = m) = ∅ :=
    Finset.filter_eq_empty_iff.mpr h
  rw [he, Finset.sum_empty]

theorem selectedCoefficient_abs_le_one (A : Finset (Finset ℕ))
    (hA : ∀ s ∈ A, ∀ p ∈ s, p.Prime) (m : ℕ) :
    |selectedCoefficient A m| ≤ 1 := by
  by_cases he : ∃ s ∈ A, subsetProduct s = m
  · obtain ⟨s, hs, rfl⟩ := he
    rw [selectedCoefficient_eq_sign A hA s hs]
    simp
  · rw [selectedCoefficient_eq_zero A m (by simpa using he)]
    norm_num

theorem selectedCoefficient_nonzero_representation (A : Finset (Finset ℕ)) (m : ℕ)
    (h : selectedCoefficient A m ≠ 0) : ∃ s ∈ A, subsetProduct s = m := by
  by_contra he
  exact h (selectedCoefficient_eq_zero A m (by simpa using he))

theorem selectedCoefficient_shared_sign (A B : Finset (Finset ℕ))
    (hA : ∀ s ∈ A, ∀ p ∈ s, p.Prime) (hB : ∀ s ∈ B, ∀ p ∈ s, p.Prime)
    (m : ℕ) : selectedCoefficient A m = 0 ∨ selectedCoefficient B m = 0 ∨
      selectedCoefficient A m = selectedCoefficient B m := by
  by_cases ha : selectedCoefficient A m = 0
  · exact Or.inl ha
  by_cases hb : selectedCoefficient B m = 0
  · exact Or.inr (Or.inl hb)
  obtain ⟨s, hs, hsm⟩ := selectedCoefficient_nonzero_representation A m ha
  obtain ⟨t, ht, htm⟩ := selectedCoefficient_nonzero_representation B m hb
  have hst := prime_subset_product_injective s t (hA s hs) (hB t ht) (hsm.trans htm.symm)
  subst t
  subst m
  exact Or.inr (Or.inr ((selectedCoefficient_eq_sign A hA s hs).trans
    (selectedCoefficient_eq_sign B hB s ht).symm))

/-- The level conclusion is obtained from an explicit restriction on the selected subsets. -/
theorem selectedCoefficient_support_level (A : Finset (Finset ℕ)) (D m : ℕ)
    (hlevel : ∀ s ∈ A, subsetProduct s < D) (hm : D ≤ m) :
    selectedCoefficient A m = 0 := by
  apply selectedCoefficient_eq_zero
  intro s hs he
  have := hlevel s hs
  omega

theorem selectedCoefficient_one (A : Finset (Finset ℕ))
    (hA : ∀ s ∈ A, ∀ p ∈ s, p.Prime) (he : ∅ ∈ A) :
    selectedCoefficient A 1 = 1 := by
  simpa [subsetProduct] using selectedCoefficient_eq_sign A hA ∅ he

theorem selectedCoefficient_support_positive (A : Finset (Finset ℕ))
    (hA : ∀ s ∈ A, ∀ p ∈ s, p.Prime) (m : ℕ)
    (hm : selectedCoefficient A m ≠ 0) : 0 < m := by
  obtain ⟨s, hs, rfl⟩ := selectedCoefficient_nonzero_representation A m hm
  exact Finset.prod_pos (fun p hp => (hA s hs p hp).pos)

#print axioms selectedCoefficient_shared_sign
#print axioms selectedCoefficient_abs_le_one
run_cmd do
  for target in [``prime_subset_product_injective, ``selectedCoefficient_eq_sign,
      ``selectedCoefficient_eq_zero, ``selectedCoefficient_abs_le_one,
      ``selectedCoefficient_nonzero_representation, ``selectedCoefficient_shared_sign,
      ``selectedCoefficient_support_level, ``selectedCoefficient_one,
      ``selectedCoefficient_support_positive] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
run_cmd Lean.logInfo "SIEVE_PRIME_SUBSET_PASSED; SELECTOR_AND_MAIN_TERM_NOT_ASSUMED"
end SievePrimeSubset
end
