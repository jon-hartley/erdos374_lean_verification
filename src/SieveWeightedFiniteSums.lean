import SieveWeightedCutoffs
import PrimeReciprocalWeightedTransfer
import SieveFullCutoffTransfer

/-! The two actual ordinary upper-selector main terms on finite source
prime ranges. This does not estimate their signed divisor remainders or
construct the separate boxed upper families. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Real Filter
open scoped BigOperators Topology
namespace SieveWeightedMainTerms
open SieveWeightedScalarBudget SieveWeightedCutoffs SieveStoppingExpansion

def mass (X s : ℝ) (S : Finset ℕ) (w : ℝ → ℝ) : ℝ :=
  ∑ p ∈ S, (p:ℝ)⁻¹*SieveFullCutoffTransfer.fullUpper (level X s/(p:ℝ)) (w p)

theorem weighted_sum_bound (S : Finset ℕ) (F d : ℕ → ℝ) (A V B : ℝ)
    (hA : 0 ≤ A) (hV : 0 ≤ V)
    (hF : ∀ p ∈ S, F p ≤ (A/d p)*V)
    (hB : (∑ p ∈ S, (p:ℝ)⁻¹/d p) ≤ B) :
    (∑ p ∈ S, (p:ℝ)⁻¹*F p) ≤ A*V*B := by
  calc
    _ ≤ ∑ p ∈ S, (p:ℝ)⁻¹*((A/d p)*V) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (hF p hp) (by positivity)
    _ = A*V*(∑ p ∈ S, (p:ℝ)⁻¹/d p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hB (mul_nonneg hA hV)

theorem mass_three_bound (X s Z : ℝ) (S : Finset ℕ) (hX : 1 < X)
    (hs : 0 ≤ s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ log X)
    (hZ : Z ≤ X^(1/7:ℝ))
    (hupper : ∀ z T : ℝ, Z ≤ z → z^3 ≤ T →
      SieveFullCutoffTransfer.fullUpper T z ≤ (452/375:ℝ)*primeEuler z)
    (hS : ∀ p ∈ S, p.Prime ∧ X^(9/35:ℝ) ≤ (p:ℝ) ∧ (p:ℝ) ≤ sqrt (2*X)) :
    mass X s S (cutoffThree X s) ≤
      ((452/375)*3*beta s*exp (84/log X))*primeEuler (X^alpha s)*
        (integralCoefficient (1-3*s) (9/35) (topExponent (1/log X))+
          10/((9/35)*((1-3*s)-topExponent (1/log X))*log X)) := by
  have hβ : 0 ≤ beta s := by
    have h := (exponent_geometry s hs hs1).2.2.1
    linarith
  have hparams := source_parameters X s hX hs hs1 hlog
  have hb := PrimeReciprocalWeightedTransfer.prime_weighted_bound X (9/35)
    (topExponent (1/log X)) (1-3*s) S hX (by norm_num)
    hparams.2.2.2.1 hparams.2.2.2.2.1 (by
      intro p hp
      obtain ⟨hpp, hlo, hhi⟩ := hS p hp
      exact ⟨hpp, hlo, hhi.trans_eq (sqrt_eq_top_power X hX)⟩)
  apply weighted_sum_bound S _ _ _ _ _ (by positivity) (SieveEulerRatio.euler_pos _).le ?_ hb
  intro p hp
  obtain ⟨_hpp, hlo, hhi⟩ := hS p hp
  obtain ⟨hcut, _hcutup, hlev⟩ := three_geometry X s p hX hs hs1 hlog hlo hhi
  have hu := hupper _ _ (hZ.trans hcut) hlev
  have he := (div_le_iff₀ (SieveEulerRatio.euler_pos (X^alpha s))).mp
    (euler_three X s p hX hs hs1 hlog hlo hhi)
  apply hu.trans
  apply (mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ) ≤ 452/375)).trans_eq
  ring

theorem mass_four_bound (X s Z : ℝ) (S : Finset ℕ) (hX : 1 < X)
    (hs : 0 ≤ s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ log X)
    (hZ : Z ≤ X^(1/7:ℝ))
    (hupper : ∀ z T : ℝ, Z ≤ z → z^3 ≤ T →
      SieveFullCutoffTransfer.fullUpper T z ≤ (452/375:ℝ)*primeEuler z)
    (hS : ∀ p ∈ S, p.Prime ∧ X^alpha s ≤ (p:ℝ) ∧ (p:ℝ) ≤ X^(9/35:ℝ)) :
    mass X s S (cutoffFour X s) ≤
      ((452/375)*2*beta s*exp (84/log X))*primeEuler (X^alpha s)*
        (integralCoefficient (upperExponent s) (alpha s) (9/35)+
          10/(alpha s*(upperExponent s-9/35)*log X)) := by
  have hβ : 0 ≤ beta s := by
    have h := (exponent_geometry s hs hs1).2.2.1
    linarith
  have ha : 0 < alpha s := by
    have h := (exponent_geometry s hs hs1).1
    linarith
  have hab : alpha s ≤ (9/35:ℝ) := by unfold alpha; linarith
  have hbk : (9/35:ℝ) < upperExponent s := by unfold upperExponent; linarith
  have hb := PrimeReciprocalWeightedTransfer.prime_weighted_bound X (alpha s)
    (9/35) (upperExponent s) S hX ha hab hbk hS
  apply weighted_sum_bound S _ _ _ _ _ (by positivity) (SieveEulerRatio.euler_pos _).le ?_ hb
  intro p hp
  obtain ⟨_hpp, hlo, hhi⟩ := hS p hp
  obtain ⟨hcut, _hcutup, hlev⟩ := four_geometry X s p hX hs hs1 hlo hhi
  have hu := hupper _ _ (hZ.trans hcut) hlev
  have he := (div_le_iff₀ (SieveEulerRatio.euler_pos (X^alpha s))).mp
    (euler_four X s p hX hs hs1 hlog hlo hhi)
  apply hu.trans
  apply (mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ) ≤ 452/375)).trans_eq
  ring

theorem combined_bound (X s Z : ℝ) (S₂ S₃ : Finset ℕ) (hX : 1 < X)
    (hs : 0 ≤ s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ log X)
    (hZ : Z ≤ X^(1/7:ℝ))
    (hupper : ∀ z T : ℝ, Z ≤ z → z^3 ≤ T →
      SieveFullCutoffTransfer.fullUpper T z ≤ (452/375:ℝ)*primeEuler z)
    (hS₂ : ∀ p ∈ S₂, p.Prime ∧ X^(9/35:ℝ) ≤ (p:ℝ) ∧ (p:ℝ) ≤ sqrt (2*X))
    (hS₃ : ∀ p ∈ S₃, p.Prime ∧ X^alpha s ≤ (p:ℝ) ∧ (p:ℝ) ≤ X^(9/35:ℝ)) :
    mass X s S₂ (cutoffThree X s)+mass X s S₃ (cutoffFour X s) ≤
      aggregate s (1/log X)*primeEuler (X^alpha s) := by
  have h := add_le_add (mass_three_bound X s Z S₂ hX hs hs1 hlog hZ hupper hS₂)
    (mass_four_bound X s Z S₃ hX hs hs1 hlog hZ hupper hS₃)
  apply h.trans_eq
  unfold aggregate
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

run_cmd do
  for decl in [``weighted_sum_bound, ``mass_three_bound, ``mass_four_bound,
      ``combined_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL FINITE WEIGHTED UPPER SUM TRANSFER; UPPER SELECTOR BOUND EXPLICIT"
end SieveWeightedMainTerms
end
