import SieveRosser
import Mathlib.Data.List.Induction

/-! The level support of the actual cubic selectors, derived from the tests.
The base list is descending, consists of positive integers, and lies below D.
Distinctness is needed only when passing from sublists to finite subsets. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators

namespace SieveRosser

theorem cubic_dominates_pair (p q : ℕ) (hp : 1 ≤ p) (hq : q ≤ p) :
    p*q ≤ p^3 := by
  calc
    p*q ≤ p*p := Nat.mul_le_mul_left p hq
    _ = p^2 := by ring
    _ ≤ p^3 := Nat.pow_le_pow_right hp (by decide)

theorem lower_accepted_product_lt (D : ℝ) (d : ℕ) (qs : List ℕ)
    (horder : qs.Pairwise (fun p q => q ≤ p))
    (hpos : ∀ p ∈ qs, 1 ≤ p) (hd : (d : ℝ) < D)
    (hroom : ∀ p ∈ qs, ((d*p : ℕ) : ℝ) < D)
    (ha : SievePrefix.accepts (cubicGate D) false d qs) :
    ((d*qs.prod : ℕ) : ℝ) < D := by
  induction qs using List.twoStepInduction generalizing d with
  | nil => simpa using hd
  | singleton p => simpa using hroom p (by simp)
  | cons_cons p q qs ih _ =>
    obtain ⟨hg, hrest⟩ := (lower_pair_test D d p q qs).mp ha
    have hq : 1 ≤ q := hpos q (by simp)
    have hqpow : q ≤ q^3 := le_self_pow hq (by decide)
    have hdnew : ((d*p*q : ℕ) : ℝ) < D := by
      exact lt_of_le_of_lt (by exact_mod_cast Nat.mul_le_mul_left (d*p) hqpow) hg
    have htailorder := (List.pairwise_cons.mp (List.pairwise_cons.mp horder).2)
    have hroomnew : ∀ r ∈ qs, ((d*p*q*r : ℕ) : ℝ) < D := by
      intro r hr
      have hqr := cubic_dominates_pair q r hq (htailorder.1 r hr)
      have hmul : d*p*q*r ≤ d*p*q^3 := by
        simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (d*p) hqr
      exact lt_of_le_of_lt (by exact_mod_cast hmul) hg
    have hfinal := ih (d*p*q) htailorder.2
      (fun r hr => hpos r (by simp [hr])) hdnew hroomnew hrest
    simpa [List.prod_cons, Nat.mul_assoc] using hfinal

theorem upper_accepted_product_lt (D : ℝ) (d : ℕ) (qs : List ℕ)
    (horder : qs.Pairwise (fun p q => q ≤ p))
    (hpos : ∀ p ∈ qs, 1 ≤ p) (hd : (d : ℝ) < D)
    (ha : SievePrefix.accepts (cubicGate D) true d qs) :
    ((d*qs.prod : ℕ) : ℝ) < D := by
  cases qs with
  | nil => simpa using hd
  | cons p ps =>
    obtain ⟨hg, hrest⟩ := (upper_first_test D d p ps).mp ha
    obtain ⟨hporder, htailorder⟩ := List.pairwise_cons.mp horder
    have hp : 1 ≤ p := hpos p (by simp)
    have hppow : p ≤ p^3 := le_self_pow hp (by decide)
    have hdnew : ((d*p : ℕ) : ℝ) < D :=
      lt_of_le_of_lt (by exact_mod_cast Nat.mul_le_mul_left d hppow) hg
    have hroom : ∀ q ∈ ps, ((d*p*q : ℕ) : ℝ) < D := by
      intro q hq
      have hpq := cubic_dominates_pair p q hp (hporder q hq)
      have hmul : d*p*q ≤ d*p^3 := by
        simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left d hpq
      exact lt_of_le_of_lt (by exact_mod_cast hmul) hg
    have hfinal := lower_accepted_product_lt D (d*p) ps htailorder
      (fun q hq => hpos q (by simp [hq])) hdnew hroom hrest
    simpa [List.prod_cons, Nat.mul_assoc] using hfinal

theorem selected_product_lt (D : ℝ) (upper : Bool) (ps : List ℕ)
    (hD : 1 < D) (hnd : ps.Nodup)
    (horder : ps.Pairwise (fun p q => q ≤ p))
    (hpos : ∀ p ∈ ps, 1 ≤ p) (hsmall : ∀ p ∈ ps, (p : ℝ) < D)
    (s : Finset ℕ) (hs : s ∈ selected D upper ps) :
    (SievePrimeSubset.subsetProduct s : ℝ) < D := by
  obtain ⟨qs, hsub, he, ha⟩ := (mem_selected_iff D upper ps s).mp hs
  have hqnd : qs.Nodup := hsub.nodup hnd
  have hqorder := List.Pairwise.sublist hsub horder
  have hqpos : ∀ p ∈ qs, 1 ≤ p := fun p hp => hpos p (hsub.subset hp)
  have hqsmall : ∀ p ∈ qs, ((1*p : ℕ) : ℝ) < D := by
    intro p hp
    simpa using hsmall p (hsub.subset hp)
  have hprod : ((1*qs.prod : ℕ) : ℝ) < D := by
    cases upper with
    | false => exact lower_accepted_product_lt D 1 qs hqorder hqpos (by simpa using hD) hqsmall ha
    | true => exact upper_accepted_product_lt D 1 qs hqorder hqpos (by simpa using hD) ha
  have hid : SievePrimeSubset.subsetProduct s = qs.prod := by
    rw [← he, SievePrimeSubset.subsetProduct, List.prod_toFinset _ hqnd]
    simp
  simpa [hid] using hprod

theorem coefficient_eq_zero_above_level (D : ℝ) (upper : Bool) (ps : List ℕ)
    (hD : 1 < D) (hnd : ps.Nodup)
    (horder : ps.Pairwise (fun p q => q ≤ p))
    (hpos : ∀ p ∈ ps, 1 ≤ p) (hsmall : ∀ p ∈ ps, (p : ℝ) < D)
    (m : ℕ) (hm : D ≤ (m : ℝ)) : coefficient D upper ps m = 0 := by
  apply SievePrimeSubset.selectedCoefficient_eq_zero
  intro s hs he
  have hh := selected_product_lt D upper ps hD hnd horder hpos hsmall s hs
  rw [he] at hh
  exact (not_lt_of_ge hm hh).elim

#print axioms selected_product_lt
run_cmd do
  for decl in [``cubic_dominates_pair, ``lower_accepted_product_lt,
      ``upper_accepted_product_lt, ``selected_product_lt, ``coefficient_eq_zero_above_level] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end SieveRosser
end
