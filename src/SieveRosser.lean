import SievePrefixAcceptance
import SievePrimeSubset

/-! Concrete finite Rosser cubic selectors and their actual collected weights.
This is not an identification with the boxed coefficients in Harman's lemma,
and no reciprocal lower-main-term asymptotic is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators

namespace SieveRosser

def cubicGate (D : ℝ) (d p : ℕ) : Prop := ((d * p^3 : ℕ) : ℝ) < D

def selected (D : ℝ) (upper : Bool) (ps : List ℕ) : Finset (Finset ℕ) :=
  SievePrefix.selected (cubicGate D) upper 1 ps

def coefficient (D : ℝ) (upper : Bool) (ps : List ℕ) (m : ℕ) : ℝ :=
  SievePrimeSubset.selectedCoefficient (selected D upper ps) m

theorem selected_subset (D : ℝ) (upper : Bool) (ps : List ℕ) (s : Finset ℕ)
    (hs : s ∈ selected D upper ps) : s ⊆ ps.toFinset :=
  SievePrefix.selected_subset (cubicGate D) upper 1 ps s hs

theorem selected_primes (D : ℝ) (upper : Bool) (ps : List ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) (s : Finset ℕ)
    (hs : s ∈ selected D upper ps) (p : ℕ) (hp : p ∈ s) : p.Prime :=
  hprime p (List.mem_toFinset.mp (selected_subset D upper ps s hs hp))

theorem finite_sieve_bounds (D : ℝ) (ps : List ℕ) (b : ℕ → ℝ)
    (hnd : ps.Nodup) (hb : ∀ p ∈ ps, 0 ≤ b p ∧ b p ≤ 1) :
    (∑ s ∈ selected D false ps, (-1 : ℝ)^s.card * ∏ p ∈ s, b p) ≤
        ∏ p ∈ ps.toFinset, (1-b p) ∧
      (∏ p ∈ ps.toFinset, (1-b p)) ≤
        ∑ s ∈ selected D true ps, (-1 : ℝ)^s.card * ∏ p ∈ s, b p :=
  SievePrefix.value_bounds (cubicGate D) 1 ps b hnd hb

theorem coefficient_abs_le_one (D : ℝ) (upper : Bool) (ps : List ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) (m : ℕ) :
    |coefficient D upper ps m| ≤ 1 :=
  SievePrimeSubset.selectedCoefficient_abs_le_one _
    (selected_primes D upper ps hprime) m

theorem coefficient_one (D : ℝ) (upper : Bool) (ps : List ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) : coefficient D upper ps 1 = 1 :=
  SievePrimeSubset.selectedCoefficient_one _ (selected_primes D upper ps hprime)
    (SievePrefix.empty_mem_selected (cubicGate D) upper 1 ps)

theorem coefficient_shared_sign (D : ℝ) (ps : List ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) (m : ℕ) :
    coefficient D false ps m = 0 ∨ coefficient D true ps m = 0 ∨
      coefficient D false ps m = coefficient D true ps m :=
  SievePrimeSubset.selectedCoefficient_shared_sign _ _
    (selected_primes D false ps hprime) (selected_primes D true ps hprime) m

theorem coefficient_positive_support (D : ℝ) (upper : Bool) (ps : List ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) (m : ℕ) (hm : coefficient D upper ps m ≠ 0) :
    0 < m :=
  SievePrimeSubset.selectedCoefficient_support_positive _
    (selected_primes D upper ps hprime) m hm

/-- In a descending base list, this is exactly the ordered selected-prime list.
No choices of a representative product or of a Cartesian box are made. -/
theorem mem_selected_iff (D : ℝ) (upper : Bool) (ps : List ℕ) (s : Finset ℕ) :
    s ∈ selected D upper ps ↔ ∃ qs : List ℕ,
      qs.Sublist ps ∧ qs.toFinset = s ∧ SievePrefix.accepts (cubicGate D) upper 1 qs :=
  SievePrefix.mem_selected_iff (cubicGate D) upper 1 ps s

/-- Lower-state tests occur at even selected-prefix lengths. -/
theorem lower_pair_test (D : ℝ) (d p q : ℕ) (qs : List ℕ) :
    SievePrefix.accepts (cubicGate D) false d (p::q::qs) ↔
      ((d*p*q^3 : ℕ) : ℝ) < D ∧
        SievePrefix.accepts (cubicGate D) false (d*p*q) qs :=
  SievePrefix.accepts_lower_cons_cons (cubicGate D) d p q qs

/-- Upper-state tests occur first at length one and then at odd lengths. -/
theorem upper_first_test (D : ℝ) (d p : ℕ) (qs : List ℕ) :
    SievePrefix.accepts (cubicGate D) true d (p::qs) ↔
      ((d*p^3 : ℕ) : ℝ) < D ∧
        SievePrefix.accepts (cubicGate D) false (d*p) qs :=
  SievePrefix.accepts_upper_cons (cubicGate D) d p qs

theorem lower_four_tests (D : ℝ) (p1 p2 p3 p4 : ℕ) :
    SievePrefix.accepts (cubicGate D) false 1 [p1,p2,p3,p4] ↔
      ((p1*p2^3 : ℕ) : ℝ) < D ∧ ((p1*p2*p3*p4^3 : ℕ) : ℝ) < D := by
  simp [SievePrefix.accepts, cubicGate]

#print axioms finite_sieve_bounds
#print axioms coefficient_abs_le_one
run_cmd do
  for decl in [``selected_subset, ``selected_primes, ``finite_sieve_bounds,
      ``coefficient_abs_le_one, ``coefficient_one, ``coefficient_shared_sign,
      ``coefficient_positive_support, ``mem_selected_iff, ``lower_pair_test,
      ``upper_first_test, ``lower_four_tests] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end SieveRosser
end
