import SievePrimeSubset
import Mathlib.Data.Nat.GCD.BigOperators

/-! Exact evaluation of the collected finite coefficient. No sieve inequality,
main term, or selection rule is assumed. Grouping retains all selected subsets. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open scoped BigOperators

namespace SievePrimeSubset

def selectedSupport (A : Finset (Finset ℕ)) : Finset ℕ := A.image subsetProduct

theorem mem_selectedSupport (A : Finset (Finset ℕ)) (m : ℕ) :
    m ∈ selectedSupport A ↔ ∃ s ∈ A, subsetProduct s = m := by
  simp only [selectedSupport, Finset.mem_image]

theorem selectedCoefficient_zero_of_not_mem (A : Finset (Finset ℕ)) (m : ℕ)
    (hm : m ∉ selectedSupport A) : selectedCoefficient A m = 0 := by
  apply selectedCoefficient_eq_zero
  intro s hs he
  exact hm ((mem_selectedSupport A m).mpr ⟨s, hs, he⟩)

theorem selectedSupport_positive (A : Finset (Finset ℕ))
    (hA : ∀ s ∈ A, ∀ p ∈ s, p.Prime) (m : ℕ) (hm : m ∈ selectedSupport A) :
    0 < m := by
  obtain ⟨s, hs, rfl⟩ := (mem_selectedSupport A m).mp hm
  exact Finset.prod_pos (fun p hp => (hA s hs p hp).pos)

theorem selectedSupport_lt_level (A : Finset (Finset ℕ)) (D : ℕ)
    (hlevel : ∀ s ∈ A, subsetProduct s < D) :
    ∀ m ∈ selectedSupport A, m < D := by
  intro m hm
  obtain ⟨s, hs, rfl⟩ := (mem_selectedSupport A m).mp hm
  exact hlevel s hs

/-- This collection identity does not need product injectivity or primality. -/
theorem sum_selectedCoefficient_kernel (A : Finset (Finset ℕ)) (b : ℕ → ℝ) :
    (∑ m ∈ selectedSupport A, selectedCoefficient A m * b m) =
      ∑ s ∈ A, (-1 : ℝ)^s.card * b (subsetProduct s) := by
  calc
    _ = ∑ s ∈ A, ∑ m ∈ selectedSupport A,
        (if subsetProduct s = m then (-1 : ℝ)^s.card else 0) * b m := by
      simp only [selectedCoefficient, Finset.sum_filter, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.sum_eq_single_of_mem (subsetProduct s)
        ((mem_selectedSupport A _).mpr ⟨s, hs, rfl⟩)]
      · simp
      · intro m hm hne
        simp [Ne.symm hne]

/-- A larger finite support changes no coefficient, and preserves every term. -/
theorem sum_selectedCoefficient_kernel_on (A : Finset (Finset ℕ))
    (T : Finset ℕ) (hT : selectedSupport A ⊆ T) (b : ℕ → ℝ) :
    (∑ m ∈ T, selectedCoefficient A m * b m) =
      ∑ s ∈ A, (-1 : ℝ)^s.card * b (subsetProduct s) := by
  calc
    _ = ∑ m ∈ selectedSupport A, selectedCoefficient A m * b m := by
      symm
      apply Finset.sum_subset hT
      intro m hm hnot
      rw [selectedCoefficient_zero_of_not_mem A m hnot, zero_mul]
    _ = _ := sum_selectedCoefficient_kernel A b

/-- Arbitrary weights on individual primes give the exact selected-subset sum. -/
theorem sum_selectedCoefficient_primeFactors (A : Finset (Finset ℕ))
    (hA : ∀ s ∈ A, ∀ p ∈ s, p.Prime) (b : ℕ → ℝ) :
    (∑ m ∈ selectedSupport A, selectedCoefficient A m * ∏ p ∈ m.primeFactors, b p) =
      ∑ s ∈ A, (-1 : ℝ)^s.card * ∏ p ∈ s, b p := by
  rw [sum_selectedCoefficient_kernel]
  apply Finset.sum_congr rfl
  intro s hs
  have he : (subsetProduct s).primeFactors = s := by
    simpa only [subsetProduct] using Nat.primeFactors_prod (hA s hs)
  rw [he]

theorem sum_selectedCoefficient_dvd (A : Finset (Finset ℕ)) (n : ℕ) :
    (∑ m ∈ selectedSupport A, if m ∣ n then selectedCoefficient A m else 0) =
      ∑ s ∈ A, if subsetProduct s ∣ n then (-1 : ℝ)^s.card else 0 := by
  simpa only [mul_ite, mul_one, mul_zero] using
    sum_selectedCoefficient_kernel A (fun m => if m ∣ n then 1 else 0)

/-- Distinct prime factors divide their product jointly exactly when each does. -/
theorem subsetProduct_dvd_iff (s : Finset ℕ) (n : ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    subsetProduct s ∣ n ↔ ∀ p ∈ s, p ∣ n := by
  revert hs
  induction s using Finset.induction_on with
  | empty =>
      intro hs
      simp [subsetProduct]
  | @insert p s hp ih =>
      intro hs
      have hpprime : p.Prime := hs p (Finset.mem_insert_self _ _)
      have hsprime : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
      constructor
      · intro h q hq
        exact (Finset.dvd_prod_of_mem (fun r : ℕ => r) hq).trans h
      · intro h
        have hc : p.Coprime (subsetProduct s) := by
          apply Nat.coprime_prod_right_iff.mpr
          intro q hq
          apply (Nat.coprime_primes hpprime (hsprime q hq)).mpr
          intro he
          exact hp (he ▸ hq)
        have hpd : p ∣ n := h p (Finset.mem_insert_self _ _)
        have hsd : subsetProduct s ∣ n :=
          (ih hsprime).mpr (fun q hq => h q (Finset.mem_insert_of_mem hq))
        simpa only [subsetProduct, Finset.prod_insert hp] using
          hc.mul_dvd_of_dvd_of_dvd hpd hsd

theorem prod_divisibility_indicator (s : Finset ℕ) (n : ℕ) :
    (∏ p ∈ s, if p ∣ n then (1 : ℝ) else 0) =
      if ∀ p ∈ s, p ∣ n then 1 else 0 := by
  by_cases h : ∀ p ∈ s, p ∣ n
  · rw [ite_eq_left h]
    exact Finset.prod_eq_one (fun p hp => ite_eq_left (h p hp))
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨p, hp, hn⟩ := h
    exact Finset.prod_eq_zero hp (ite_eq_right hn)

/-- Literal divisor testing of the constructed coefficient is exactly the
alternating selected-subset polynomial at the actual 0/1 divisibility vector. -/
theorem selectedCoefficient_dvd_eq_product (A : Finset (Finset ℕ))
    (hA : ∀ s ∈ A, ∀ p ∈ s, p.Prime) (n : ℕ) :
    (∑ m ∈ selectedSupport A, if m ∣ n then selectedCoefficient A m else 0) =
      ∑ s ∈ A, (-1 : ℝ)^s.card *
        ∏ p ∈ s, if p ∣ n then (1 : ℝ) else 0 := by
  rw [sum_selectedCoefficient_dvd]
  apply Finset.sum_congr rfl
  intro s hs
  rw [prod_divisibility_indicator]
  by_cases hd : subsetProduct s ∣ n
  · have hall := (subsetProduct_dvd_iff s n (hA s hs)).mp hd
    rw [ite_eq_left hd, ite_eq_left hall, mul_one]
  · have hnot : ¬ ∀ p ∈ s, p ∣ n :=
      fun hall => hd ((subsetProduct_dvd_iff s n (hA s hs)).mpr hall)
    rw [ite_eq_right hd, ite_eq_right hnot, mul_zero]

#print axioms sum_selectedCoefficient_kernel
#print axioms selectedCoefficient_dvd_eq_product
run_cmd do
  for decl in [``mem_selectedSupport, ``selectedCoefficient_zero_of_not_mem,
      ``selectedSupport_positive, ``selectedSupport_lt_level,
      ``sum_selectedCoefficient_kernel, ``sum_selectedCoefficient_kernel_on,
      ``sum_selectedCoefficient_primeFactors, ``sum_selectedCoefficient_dvd,
      ``subsetProduct_dvd_iff, ``prod_divisibility_indicator,
      ``selectedCoefficient_dvd_eq_product] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
run_cmd Lean.logInfo "SIEVE_PRIME_SUBSET_EVALUATION_PASSED; FINITE_IDENTITIES_ONLY"

end SievePrimeSubset
end
