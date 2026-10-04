import LongerTupleDyadic
import PolynomialLogEnvelope

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter
open scoped BigOperators

namespace LongPairEdgeDyadicWork
open FourPrimePartition LongerTupleDyadic

theorem eventually_data :
    ∀ᶠ X : ℝ in atTop, 1≤X ∧ ∀ (S T : Finset ℕ) (R : ℕ → ℕ → Prop),
      (∀ m∈S,∀ q∈T,R m q →
        X^(545/1000:ℝ)≤(m:ℝ)*(q:ℝ) ∧ X^(8/35:ℝ)≤(q:ℝ) ∧
        (q:ℝ)≤X^(229/1000:ℝ) ∧ (m:ℝ)*(q:ℝ)≤X^(772/1000:ℝ)) →
      ∀ ij∈jointFamily X S T R,
        1≤scale 1 ij.1 ∧ 1≤scale 1 ij.2 ∧
        X^(1/2:ℝ)≤((scale 1 ij.1*scale 1 ij.2:ℕ):ℝ) ∧
        ((scale 1 ij.1*scale 1 ij.2:ℕ):ℝ)≤X^(772/1000:ℝ) ∧
        X^(1/5:ℝ)≤(scale 1 ij.2:ℝ) ∧
        (scale 1 ij.2:ℝ)≤X^(229/1000:ℝ) ∧
        (∀ n∈block S 1 ij.1,scale 1 ij.1<n ∧ n≤2*scale 1 ij.1) ∧
        (∀ n∈block T 1 ij.2,scale 1 ij.2<n ∧ n≤2*scale 1 ij.2) := by
  filter_upwards [PolynomialLogEnvelope.eventually_constant_bound 4
      ((545/1000:ℝ)-1/2) (by norm_num) (by norm_num),
    PolynomialLogEnvelope.eventually_constant_bound 2
      ((8/35:ℝ)-1/5) (by norm_num) (by norm_num)] with X hm hn
  refine ⟨hm.1,?_⟩
  intro S T R hR ij hij
  obtain ⟨_,m,hmb,q,hqb,hr⟩ := (mem_jointFamily X S T R ij).mp hij
  obtain ⟨hms,hmlo,hmhi⟩ := (mem_block S 1 ij.1 m).mp hmb
  obtain ⟨hqs,hnlo,hnhi⟩ := (mem_block T 1 ij.2 q).mp hqb
  obtain ⟨hplow,hqlow,hqcap,hprod⟩ := hR m hms q hqs hr
  have hX0 : 0<X := by linarith [hm.1]
  have hP : 4*X^(1/2:ℝ)≤X^(545/1000:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hm.2 (Real.rpow_pos_of_pos hX0 (1/2:ℝ)).le
    rw [←Real.rpow_add hX0,sub_add_cancel] at hh
    exact hh
  have hN : 2*X^(1/5:ℝ)≤X^(8/35:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hn.2 (Real.rpow_pos_of_pos hX0 (1/5:ℝ)).le
    rw [←Real.rpow_add hX0,sub_add_cancel] at hh
    exact hh
  have hhiProd : (m:ℝ)*(q:ℝ)≤4*((scale 1 ij.1*scale 1 ij.2:ℕ):ℝ) := by
    have hh := Nat.mul_le_mul hmhi hnhi
    exact_mod_cast (by nlinarith : m*q≤4*(scale 1 ij.1*scale 1 ij.2))
  have hloProd : ((scale 1 ij.1*scale 1 ij.2:ℕ):ℝ)≤(m:ℝ)*(q:ℝ) := by
    exact_mod_cast Nat.mul_le_mul hmlo.le hnlo.le
  have hnhiR : (q:ℝ)≤2*(scale 1 ij.2:ℝ) := by exact_mod_cast hnhi
  have hnloR : (scale 1 ij.2:ℝ)≤(q:ℝ) := by exact_mod_cast hnlo.le
  exact ⟨scale_pos 1 ij.1 (by norm_num),scale_pos 1 ij.2 (by norm_num),
    by linarith, hloProd.trans hprod, by linarith,hnloR.trans hqcap,
    block_bounds S 1 ij.1,block_bounds T 1 ij.2⟩

run_cmd do
  for ax in (←Lean.collectAxioms ``eventually_data) do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"

end LongPairEdgeDyadicWork
