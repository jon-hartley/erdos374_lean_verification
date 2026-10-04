import LongerTupleDyadic
import TripleFlatParameters

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter
open scoped BigOperators

namespace LongPairFlatDyadicWork
open FourPrimePartition LongerTupleDyadic TripleFlatParameters

theorem eventually_data :
    ∀ᶠ X : ℝ in atTop, 1≤X ∧ ∀ (S T : Finset ℕ) (R : ℕ → ℕ → Prop),
      (∀ m∈S,∀ q∈T,R m q →
        X^(47/100:ℝ)≤(m:ℝ) ∧ X^(8/35:ℝ)≤(q:ℝ) ∧
          (m:ℝ)*(q:ℝ)≤X^(26/35:ℝ)) →
      ∀ ij∈jointFamily X S T R,
        X^pairExponent≤(scale 1 ij.1:ℝ) ∧ X^primeExponent≤(scale 1 ij.2:ℝ) ∧
        ((scale 1 ij.1*scale 1 ij.2:ℕ):ℝ)≤X^(26/35:ℝ) ∧
        (∀ n∈block S 1 ij.1,scale 1 ij.1<n ∧ n≤2*scale 1 ij.1) ∧
        (∀ n∈block T 1 ij.2,scale 1 ij.2<n ∧ n≤2*scale 1 ij.2) := by
  filter_upwards [PolynomialLogEnvelope.eventually_constant_bound 2
      ((47/100:ℝ)-pairExponent) (by norm_num) (by norm_num [pairExponent]),
    PolynomialLogEnvelope.eventually_constant_bound 2
      ((8/35:ℝ)-primeExponent) (by norm_num) (by norm_num [primeExponent])]
    with X hm hn
  refine ⟨hm.1,?_⟩
  intro S T R hR ij hij
  obtain ⟨_,m,hmb,q,hqb,hr⟩ := (mem_jointFamily X S T R ij).mp hij
  obtain ⟨hms,hmlo,hmhi⟩ := (mem_block S 1 ij.1 m).mp hmb
  obtain ⟨hqs,hnlo,hnhi⟩ := (mem_block T 1 ij.2 q).mp hqb
  obtain ⟨hmlow,hqlow,hprod⟩ := hR m hms q hqs hr
  have hX0 : 0<X := by linarith [hm.1]
  have hM : 2*X^pairExponent≤X^(47/100:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hm.2 (Real.rpow_pos_of_pos hX0 pairExponent).le
    rw [←Real.rpow_add hX0,sub_add_cancel] at hh
    exact hh
  have hN : 2*X^primeExponent≤X^(8/35:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hn.2 (Real.rpow_pos_of_pos hX0 primeExponent).le
    rw [←Real.rpow_add hX0,sub_add_cancel] at hh
    exact hh
  have hmhiR : (m:ℝ)≤2*(scale 1 ij.1:ℝ) := by exact_mod_cast hmhi
  have hnhiR : (q:ℝ)≤2*(scale 1 ij.2:ℝ) := by exact_mod_cast hnhi
  refine ⟨by linarith,by linarith,?_,block_bounds S 1 ij.1,block_bounds T 1 ij.2⟩
  have hlow := Nat.mul_le_mul hmlo.le hnlo.le
  exact (by exact_mod_cast hlow : ((scale 1 ij.1*scale 1 ij.2:ℕ):ℝ)≤(m:ℝ)*q).trans hprod

run_cmd do
  for ax in (←Lean.collectAxioms ``eventually_data) do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"

end LongPairFlatDyadicWork
