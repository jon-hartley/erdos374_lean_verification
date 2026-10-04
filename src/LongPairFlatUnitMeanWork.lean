import TripleFlatContourMeanSquare
import TripleDyadicWeights
import TripleFlatParameters
import ShortSingletonComplex

/-! Unit real coefficients in the flat range, with the remaining triple
on the left and the selected long prime on the right. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace LongPairFlatUnitMeanWork
open TripleFlatParameters

theorem eventually_bound :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ X : ℝ in atTop, Real.exp 1≤X ∧
      ∀ (M N : ℕ) (sm sn : Finset ℕ) (a b : ℕ → ℝ),
        let Y : ℝ := X^(101/1000:ℝ)/2
        X^pairExponent≤(M:ℝ) → X^primeExponent≤(N:ℝ) →
        ((M*N:ℕ):ℝ)≤X^(26/35:ℝ) →
        (∀ n∈sm,M<n ∧ n≤2*M) → (∀ n∈sn,N<n ∧ n≤2*N) →
        (∀ n∈sm,|a n|≤1) → (∀ n∈sn,|b n|≤1) →
        (1/X)*(∫ x in Icc X (2*X), HarmanDivisorWindow.remainder
          (FactoredDivisorWeights.support sm sn) (FactoredDivisorWeights.coefficient sm sn a b)
            (x-x*(Y/X)) x ^ 2) ≤ Y^2*X^(-c) := by
  obtain ⟨c,hc,ε,hε,hmean⟩ := TripleFlatContourMeanSquare.eventually_bound
  refine ⟨c,hc,?_⟩
  filter_upwards [hmean,TripleFlatParameters.eventually_half_width,
    TripleDyadicWeights.eventually_coefficient_cap
      TripleFlatContourMeanSquare.coefficientExponent
      TripleFlatContourMeanSquare.coefficientExponent_pos] with X hm hY hcap
  refine ⟨hm.1,?_⟩
  intro M N sm sn a b
  dsimp only
  intro hM hN hA hsm hsn ha hb
  have hX : 1≤X := by linarith [Real.add_one_le_exp (1:ℝ),hm.1]
  have hAX : ((N*M:ℕ):ℝ)≤X := by
    have hAN : ((N*M:ℕ):ℝ)≤X^(26/35:ℝ) := by simpa only [Nat.mul_comm] using hA
    apply hAN.trans
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX
      (by norm_num : (26/35:ℝ)≤1)
  have hMpos : 1≤M := by
    have hh := (Real.one_le_rpow hX (by norm_num [pairExponent] : 0≤pairExponent)).trans hM
    exact_mod_cast hh
  have hunit : 1≤X^(TripleFlatContourMeanSquare.coefficientExponent/8) :=
    Real.one_le_rpow hX (by positivity [TripleFlatContourMeanSquare.coefficientExponent_pos])
  have hweights := hcap.2 N M sn sm b a hMpos hAX hsn hsm
    (fun n hn => (hb n hn).trans hunit) (fun n hn => (ha n hn).trans hunit)
  have hsqa := TripleDyadicWeights.energy X ε 0 M sm a hX (by linarith) hsm
    (by simpa only [Real.rpow_zero] using ha)
  have hsqb := TripleDyadicWeights.energy X ε 0 N sn b hX (by linarith) hsn
    (by simpa only [Real.rpow_zero] using hb)
  have hh := hm.2 N M sn sm b a (X^(101/1000:ℝ)/2) hN hM
    (by simpa only [Nat.mul_comm] using hA) hY.1 hY.2 hsn hsm hsqb hsqa hweights
  have he (L R : ℝ) : HarmanDivisorWindow.remainder
      (FactoredDivisorWeights.support sm sn) (FactoredDivisorWeights.coefficient sm sn a b) L R =
      HarmanDivisorWindow.remainder (FactoredDivisorWeights.support sn sm)
        (FactoredDivisorWeights.coefficient sn sm b a) L R := by
    change ShortSingletonComplex.realRemainder sm sn a b L R =
      ShortSingletonComplex.realRemainder sn sm b a L R
    rw [ShortSingletonComplex.realRemainder_eq_sum,ShortSingletonComplex.realRemainder_eq_sum]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  simp_rw [he]
  exact hh

#print axioms eventually_bound
run_cmd do
  for ax in (←Lean.collectAxioms ``eventually_bound) do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"

end LongPairFlatUnitMeanWork
