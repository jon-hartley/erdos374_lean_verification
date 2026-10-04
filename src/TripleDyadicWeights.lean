import FactoredDivisorWeights
import NormalizedDyadicCap

/-! Subpower factor weights give the two energies and the full signed
convolution cap. No representation is removed when products coincide. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter
open scoped BigOperators

namespace TripleDyadicWeights

theorem energy (X ε δ : ℝ) (M : ℕ) (S : Finset ℕ) (a : ℕ → ℝ)
    (hX : 1 ≤ X) (hδε : 2 * δ ≤ ε)
    (hS : ∀ n ∈ S, M < n ∧ n ≤ 2 * M)
    (ha : ∀ n ∈ S, |a n| ≤ X ^ δ) :
    (∑ n ∈ S, a n ^ 2) ≤ X ^ ε * M := by
  have hXp : 0 < X := by linarith
  have hpow : (X ^ δ) ^ (2 : ℕ) ≤ X ^ ε := by
    rw [← Real.rpow_mul_natCast hXp.le]
    apply Real.rpow_le_rpow_of_exponent_le hX
    norm_num
    linarith
  calc
    _ ≤ ∑ _n ∈ S, X ^ ε := by
      apply Finset.sum_le_sum
      intro n hn
      have hh := pow_le_pow_left₀ (abs_nonneg (a n)) (ha n hn) 2
      rw [sq_abs] at hh
      exact hh.trans hpow
    _ = (S.card : ℝ) * X ^ ε := by simp
    _ ≤ (M : ℝ) * X ^ ε := mul_le_mul_of_nonneg_right
      (NormalizedDyadicCap.card_bound S M hS) (Real.rpow_nonneg hXp.le _)
    _ = _ := mul_comm _ _

theorem eventually_coefficient_cap (β : ℝ) (hβ : 0 < β) :
    ∀ᶠ X : ℝ in atTop, 4 ≤ X ∧
      ∀ (M N : ℕ) (S T : Finset ℕ) (a b : ℕ → ℝ),
        1 ≤ N → ((M * N : ℕ) : ℝ) ≤ X →
        (∀ n ∈ S, M < n ∧ n ≤ 2 * M) →
        (∀ n ∈ T, N < n ∧ n ≤ 2 * N) →
        (∀ n ∈ S, |a n| ≤ X ^ (β / 8)) →
        (∀ n ∈ T, |b n| ≤ X ^ (β / 8)) →
        ∀ d ∈ FactoredDivisorWeights.support S T,
          |FactoredDivisorWeights.coefficient S T a b d| ≤ X ^ β := by
  filter_upwards [ProductCoefficientCap.eventually_bound β hβ,
    eventually_ge_atTop (4 : ℝ)] with X hh hX
  refine ⟨hX, ?_⟩
  intro M N S T a b hN hMN hS hT ha hb d hd
  have hbound := FactoredDivisorWeights.support_bounds M N S T hN hS hT d hd
  have hdp : 0 < d := by omega
  have hdX : (d : ℝ) ≤ X ^ (2 : ℕ) := by
    have hd4 : (d : ℝ) ≤ 4 * ((M * N : ℕ) : ℝ) := by
      exact_mod_cast (by simpa only [mul_assoc] using hbound.2 : d ≤ 4 * (M * N))
    nlinarith
  have hc := hh.2 S T (fun n => (a n : ℂ)) (fun n => (b n : ℂ)) d hdp hdX
    (fun n hn => by simpa only [Complex.norm_real, Real.norm_eq_abs] using ha n hn)
    (fun n hn => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hb n hn)
  rw [← FactoredDivisorWeights.coefficient_cast] at hc
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hc

run_cmd do
  for decl in [``energy, ``eventually_coefficient_cap] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "TRIPLE DYADIC SIGNED WEIGHTS AND ENERGY PASSED"

end TripleDyadicWeights
