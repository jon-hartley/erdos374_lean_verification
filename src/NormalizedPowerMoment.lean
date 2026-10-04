import NormalizedPowerLevel
import NormalizedEvenMoment
import MomentThreshold

/-!
Intermediate moments of actual polynomial powers. Both the large-value
measure and the lower even moment are proved, with all losses explicit.
The supplied supremum cap remains an application condition.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace NormalizedPowerMoment
open Erdos374.HarmanGram152 DirichletLargeValueMeasure DyadicLevelParameters
open NormalizedPowerLevel SupremumMoment MomentThreshold

theorem integral_bound (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (s : Finset ℕ) (N : ℕ) (coeff : ℕ → ℂ) (a T A σ U p μ : ℝ),
      1 ≤ N → 0 < T → 0 < A → 1 ≤ σ → 0 ≤ U → 2 ≤ p → p < 6 → 0 < μ →
      (∀ n ∈ s, N < n ∧ n ≤ 2 * N) →
      (∑ n ∈ s, ‖coeff n‖ ^ 2) ≤ A * N →
      (∀ t ∈ Icc a (a + T), ‖verticalDirichlet152 s coeff σ t‖ ^ k ≤ U) →
      U ^ (p - 2) ≤ μ →
      let E := energyBudget D N k ε A
      let Q := quadratic (N ^ k) k T E
      let B := sextic (N ^ k) k T E
      (∫ t in Icc a (a + T), ‖verticalDirichlet152 s coeff σ t‖ ^ ((k : ℝ) * p)) ≤
        (B / μ) ^ ((p - 2) / (6 - p)) *
          (C * (2 * (N : ℝ)) ^ ε * A ^ k *
            (T / (N : ℝ) ^ k + 4 * (2 : ℝ) ^ k * (1 + k * Real.log (2 * N)))) +
        bandCountBound (cutoff B μ p) U * (2 : ℝ) ^ p *
          (Q * (2 : ℝ) ^ (p - 2) + 1) * μ := by
  obtain ⟨D, hD, hlevel⟩ := NormalizedPowerLevel.measure_bound k hk ε hε
  obtain ⟨C, hC, hmean⟩ := NormalizedEvenMoment.integral_bound k hk ε hε
  refine ⟨D, hD, C, hC, ?_⟩
  intro s N coeff a T A σ U p μ hN hT hA hσ hU hp hp6 hμ hs henergy hcap hpower
  let F := fun t => verticalDirichlet152 s coeff σ t ^ k
  let E := energyBudget D N k ε A
  let Q := quadratic (N ^ k) k T E
  let B := sextic (N ^ k) k T E
  have hs0 : ∀ n ∈ s, 0 < n := by
    intro n hn
    have hh := (hs n hn).1
    omega
  have hF : Continuous F := (NormalizedMeanSquare.continuous_vertical s coeff σ hs0).pow k
  have hEp : 0 < E := budget_positive D N k ε A hD hN hA
  have hQ : 0 ≤ Q := quadratic_nonnegative (N ^ k) k T E hT.le hEp.le
  have hB : 0 < B := sextic_positive (N ^ k) k T E (one_le_pow₀ hN) hk hT hEp
  have hc : ∀ t ∈ Icc a (a + T), ‖F t‖ ≤ U := by
    intro t ht
    simpa only [F, norm_pow] using hcap t ht
  have hl : ∀ w : ℝ, 0 < w → volume (levelSet F a T w) ≤
      ENNReal.ofReal (Q / w ^ 2 + B / w ^ 6) := by
    intro w hw
    exact hlevel s N coeff a T A σ w hN hT.le hA hσ hw hs henergy
  have hh := MomentThreshold.integral_bound F a T U p Q B μ
    hF hU hp hp6 hQ hB hμ hc hpower hl
  have hmeanF : (∫ t in Icc a (a + T), ‖F t‖ ^ 2) ≤
      C * (2 * (N : ℝ)) ^ ε * A ^ k *
        (T / (N : ℝ) ^ k + 4 * (2 : ℝ) ^ k * (1 + k * Real.log (2 * N))) := by
    have hm := hmean s N coeff a T A σ hN hT.le hσ
      (fun n hn => ⟨(hs n hn).1.le, (hs n hn).2⟩) henergy
    have heq (t : ℝ) : ‖F t‖ ^ 2 = ‖verticalDirichlet152 s coeff σ t‖ ^ (2 * k) := by
      dsimp [F]
      rw [norm_pow, ← pow_mul, Nat.mul_comm]
    simpa only [heq] using hm
  have heq (t : ℝ) : ‖F t‖ ^ p = ‖verticalDirichlet152 s coeff σ t‖ ^ ((k : ℝ) * p) := by
    dsimp [F]
    rw [norm_pow, ← Real.rpow_natCast_mul (norm_nonneg _)]
  simp only [heq] at hh
  apply hh.trans
  exact add_le_add (mul_le_mul_of_nonneg_left hmeanF
    (Real.rpow_nonneg (div_pos hB hμ).le _)) le_rfl

end NormalizedPowerMoment

#print axioms NormalizedPowerMoment.integral_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``NormalizedPowerMoment.integral_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "NORMALIZED POWER MOMENT PASSED"
