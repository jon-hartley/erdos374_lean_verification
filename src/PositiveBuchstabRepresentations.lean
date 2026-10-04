import Erdos374_Update152
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Literal ordered Buchstab representations. Distinct first-prime choices
remain distinct even when their products coincide. No distribution estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators
namespace PositiveBuchstabRepresentations
open Erdos374.HarmanAnalytic151

abbrev Representation := Σ _p : ℕ, Σ _q : ℕ, ℕ

def representations (A : Finset ℕ) (a b : ℕ) (z : ℕ → ℕ) : Finset Representation :=
  (primeBand a b).sigma fun p =>
    (primeBand (z p) p).sigma fun q => sifted (divisorSlice A (p*q)) q

theorem card_representations (A : Finset ℕ) (a b : ℕ) (z : ℕ → ℕ) :
    (representations A a b z).card =
      ∑ p ∈ primeBand a b, ∑ q ∈ primeBand (z p) p,
        (sifted (divisorSlice A (p*q)) q).card := by
  simp only [representations, Finset.card_sigma]

theorem mem_representations (A : Finset ℕ) (a b : ℕ) (z : ℕ → ℕ)
    (p q n : ℕ) :
    (⟨p,⟨q,n⟩⟩ : Representation) ∈ representations A a b z ↔
      p ∈ primeBand a b ∧ q ∈ primeBand (z p) p ∧
        n ∈ A ∧ p*q ∣ n ∧ Rough q n := by
  simp [representations, Finset.mem_sigma, sifted, divisorSlice, and_assoc]

theorem rough_prime (z p : ℕ) (hp : p.Prime) (hz : z ≤ p) : Rough z p := by
  intro l hl hlz hdiv
  have hEq : l=p := (Nat.prime_dvd_prime_iff_eq hl hp).mp hdiv
  subst l
  omega

theorem rough_mul (z m n : ℕ) (hm : Rough z m) (hn : Rough z n) : Rough z (m*n) := by
  intro l hl hlz hdiv
  rcases hl.dvd_mul.mp hdiv with h | h
  · exact hm l hl hlz h
  · exact hn l hl hlz h

theorem rough_triple (p r q : ℕ) (hp : p.Prime) (hr : r.Prime) (hq : q.Prime)
    (hqp : q ≤ p) (hqr : q ≤ r) : Rough q (p*r*q) :=
  rough_mul q (p*r) q
    (rough_mul q p r (rough_prime q p hp hqp) (rough_prime q r hr hqr))
    (rough_prime q q hq le_rfl)

theorem triple_mem (A : Finset ℕ) (a b : ℕ) (z : ℕ → ℕ) (p r q : ℕ)
    (hp : p ∈ primeBand a b) (hq : q ∈ primeBand (z p) p)
    (hr : r.Prime) (hqr : q ≤ r) (hA : p*r*q ∈ A) :
    (⟨p,⟨q,p*r*q⟩⟩ : Representation) ∈ representations A a b z := by
  apply (mem_representations A a b z p q (p*r*q)).mpr
  refine ⟨hp,hq,hA,?_,?_⟩
  · exact ⟨r,by ring⟩
  · exact rough_triple p r q (Finset.mem_filter.mp hp).2 hr
      (Finset.mem_filter.mp hq).2
      (Nat.le_of_lt (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).2) hqr

theorem cancel_middle (p q r r' : ℕ) (hp : 0 < p) (hq : 0 < q)
    (h : p*r*q=p*r'*q) : r=r' := by
  exact Nat.eq_of_mul_eq_mul_left hp (Nat.eq_of_mul_eq_mul_right hq h)

run_cmd do
  for decl in [``card_representations, ``mem_representations, ``rough_prime,
      ``rough_mul, ``rough_triple, ``triple_mem, ``cancel_middle] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ORDERED BUCHSTAB REPRESENTATIONS; MULTIPLICITIES RETAINED"
end PositiveBuchstabRepresentations
end
