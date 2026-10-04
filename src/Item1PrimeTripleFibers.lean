import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
UNCOMPILED PROOF-BODY DRAFT. At most six ordered prime triples per product;
repeated primes are permitted. The bound is not claimed for composite triples.
The coefficient-energy lemmas are finite and need no divisor-function estimate.
-/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators
namespace Item1PrimeTripleFibers

abbrev Triple := ℕ × ℕ × ℕ

def product (t : Triple) : ℕ := t.1*t.2.1*t.2.2

def allPrime (t : Triple) : Prop :=
  t.1.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime

def orbit (t : Triple) : Finset Triple :=
  {(t.1,t.2.1,t.2.2), (t.1,t.2.2,t.2.1),
   (t.2.1,t.1,t.2.2), (t.2.1,t.2.2,t.1),
   (t.2.2,t.1,t.2.1), (t.2.2,t.2.1,t.1)}

theorem pair_cases (p q a b : ℕ) (hp : p.Prime) (ha : a.Prime) (hb : b.Prime)
    (h : p*q=a*b) : (p=a ∧ q=b) ∨ (p=b ∧ q=a) := by
  have hd : p ∣ a*b := ⟨q,h.symm⟩
  rcases hp.dvd_mul.mp hd with hpa | hpb
  · have hap : a=p := (ha.dvd_iff_eq hp.ne_one).mp hpa
    subst a
    exact Or.inl ⟨rfl,mul_left_cancel₀ hp.ne_zero h⟩
  · have hbp : b=p := (hb.dvd_iff_eq hp.ne_one).mp hpb
    subst b
    have hh : p*q=p*a := by simpa only [mul_comm a p] using h
    exact Or.inr ⟨rfl,mul_left_cancel₀ hp.ne_zero hh⟩

theorem member_orbit_of_product_eq (t a : Triple) (ht : allPrime t)
    (ha : allPrime a) (h : product t=product a) : t ∈ orbit a := by
  rcases t with ⟨p,q,r⟩
  rcases a with ⟨a,b,c⟩
  rcases ht with ⟨hp,hq,hr⟩
  rcases ha with ⟨ha,hb,hc⟩
  change p*q*r=a*b*c at h
  have hd : p ∣ (a*b)*c := ⟨q*r, by simpa only [mul_assoc] using h.symm⟩
  rcases hp.dvd_mul.mp hd with hab | hpc
  · rcases hp.dvd_mul.mp hab with hpa | hpb
    · have hap : a=p := (ha.dvd_iff_eq hp.ne_one).mp hpa
      subst a
      have he : q*r=b*c := mul_left_cancel₀ hp.ne_zero (by simpa only [mul_assoc] using h)
      rcases pair_cases q r b c hq hb hc he with ⟨hqb,hrc⟩ | ⟨hqc,hrb⟩
      · subst q; subst r; simp [orbit]
      · subst q; subst r; simp [orbit]
    · have hbp : b=p := (hb.dvd_iff_eq hp.ne_one).mp hpb
      subst b
      have he : q*r=a*c := by
        apply mul_left_cancel₀ hp.ne_zero
        calc
          p*(q*r)=a*p*c := by simpa only [mul_assoc] using h
          _=p*(a*c) := by ring
      rcases pair_cases q r a c hq ha hc he with ⟨hqa,hrc⟩ | ⟨hqc,hra⟩
      · subst q; subst r; simp [orbit]
      · subst q; subst r; simp [orbit]
  · have hcp : c=p := (hc.dvd_iff_eq hp.ne_one).mp hpc
    subst c
    have he : q*r=a*b := by
      apply mul_left_cancel₀ hp.ne_zero
      calc
        p*(q*r)=a*b*p := by simpa only [mul_assoc] using h
        _=p*(a*b) := by ring
    rcases pair_cases q r a b hq ha hb he with ⟨hqa,hrb⟩ | ⟨hqb,hra⟩
    · subst q; subst r; simp [orbit]
    · subst q; subst r; simp [orbit]

theorem orbit_card_le (a : Triple) : (orbit a).card ≤ 6 := by
  exact Finset.card_le_six

/-- Every finite prime-only product fiber has at most six members. -/
theorem fiber_card_le (S : Finset Triple) (m : ℕ)
    (hprime : ∀ t ∈ S, allPrime t) (hprod : ∀ t ∈ S, product t=m) :
    S.card ≤ 6 := by
  classical
  by_cases hs : S.Nonempty
  · obtain ⟨a,ha⟩ := hs
    have hsub : S ⊆ orbit a := by
      intro t ht
      exact member_orbit_of_product_eq t a (hprime t ht) (hprime a ha)
        ((hprod t ht).trans (hprod a ha).symm)
    exact (Finset.card_le_card hsub).trans (orbit_card_le a)
  · have hz : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hz]

theorem fiber_weight_le (S : Finset Triple) (m : ℕ) (ell : ℝ) (w : Triple → ℝ)
    (hl : 0 ≤ ell) (hprime : ∀ t ∈ S, allPrime t)
    (hprod : ∀ t ∈ S, product t=m) (hw : ∀ t ∈ S, w t ≤ ell^3) :
    (∑ t ∈ S, w t) ≤ 6*ell^3 := by
  have hc : (S.card : ℝ) ≤ 6 := by exact_mod_cast fiber_card_le S m hprime hprod
  calc
    (∑ t ∈ S, w t) ≤ ∑ t ∈ S, ell^3 := Finset.sum_le_sum hw
    _ = (S.card : ℝ)*ell^3 := by simp
    _ ≤ 6*ell^3 := mul_le_mul_of_nonneg_right hc (by positivity)

/-- A real scalar estimate used after collecting the actual prime triples. -/
theorem coefficient_square_le (X ell n c : ℝ) (hX : 0 < X) (hl : 0 ≤ ell)
    (hn : X/8 ≤ n) (hc0 : 0 ≤ c) (hc : c ≤ 6*ell^3) :
    (c/n)^2 ≤ (48*ell^3/X)*(c/n) := by
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hb0 : 0 ≤ c/n := div_nonneg hc0 hnpos.le
  have hb : c/n ≤ 48*ell^3/X := by
    calc
      c/n ≤ (6*ell^3)/n := div_le_div_of_nonneg_right hc hnpos.le
      _ ≤ (6*ell^3)/(X/8) := div_le_div_of_nonneg_left (by positivity) (by positivity) hn
      _ = 48*ell^3/X := by field_simp <;> ring
  calc
    (c/n)^2=(c/n)*(c/n) := by ring
    _ ≤ (48*ell^3/X)*(c/n) := mul_le_mul_of_nonneg_right hb hb0

/-- Uniform actual-coefficient energy once the elementary reciprocal mass is inserted. -/
theorem coefficient_energy_le (S : Finset ℕ) (X ell : ℝ) (c : ℕ → ℝ)
    (hX : 0 < X) (hl : 0 ≤ ell)
    (hn : ∀ n ∈ S, X/8 ≤ (n:ℝ))
    (hc0 : ∀ n ∈ S, 0 ≤ c n) (hc : ∀ n ∈ S, c n ≤ 6*ell^3)
    (hmass : (∑ n ∈ S, c n/(n:ℝ)) ≤ 32*ell^3) :
    (∑ n ∈ S, (c n/(n:ℝ))^2) ≤ 1536*ell^6/X := by
  calc
    (∑ n ∈ S, (c n/(n:ℝ))^2) ≤
        ∑ n ∈ S, (48*ell^3/X)*(c n/(n:ℝ)) := by
      apply Finset.sum_le_sum
      intro n hnS
      exact coefficient_square_le X ell n (c n) hX hl (hn n hnS) (hc0 n hnS) (hc n hnS)
    _ = (48*ell^3/X)*(∑ n ∈ S, c n/(n:ℝ)) := by rw [Finset.mul_sum]
    _ ≤ (48*ell^3/X)*(32*ell^3) := mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = 1536*ell^6/X := by ring

#print axioms fiber_card_le
#print axioms coefficient_energy_le
run_cmd do
  for n in [``pair_cases, ``member_orbit_of_product_eq, ``orbit_card_le,
      ``fiber_card_le, ``fiber_weight_le, ``coefficient_square_le, ``coefficient_energy_le] do
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {n}"
end Item1PrimeTripleFibers

-- ROOT SOURCE RECURSIVE AUDIT: exact original declarations.
run_cmd do
  for target in [
    ``Item1PrimeTripleFibers.pair_cases,
    ``Item1PrimeTripleFibers.member_orbit_of_product_eq,
    ``Item1PrimeTripleFibers.orbit_card_le,
    ``Item1PrimeTripleFibers.fiber_card_le,
    ``Item1PrimeTripleFibers.fiber_weight_le,
    ``Item1PrimeTripleFibers.coefficient_square_le,
    ``Item1PrimeTripleFibers.coefficient_energy_le] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1PrimeTripleFibers: 7 original theorem guards passed."
