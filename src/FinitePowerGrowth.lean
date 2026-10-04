import NormalizedPowerGrowth

/-!
One positive coefficient-energy exponent and one eventual ambient scale
serve every integer power h between one and a fixed upper bound H.
The moment order p remains uniform over the closed interval [2,3].

The case H = 0 is only an empty induction base; applications with an
eligible power require H >= 1. This theorem retains the actual support,
energy, and length conditions and does not identify sieve terms.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace FinitePowerGrowth
open Erdos374.HarmanGram152

theorem eventually_bound (H : ℕ) (γ : ℝ) (hγ : 0 < γ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      ∀ (h : ℕ), 1 ≤ h → h ≤ H →
      ∀ (s : Finset ℕ) (N : ℕ) (coeff : ℕ → ℂ) (a T σ p : ℝ),
        1 ≤ N → (N : ℝ) ≤ X → 1 ≤ T → T ≤ X → 1 ≤ σ →
        2 ≤ p → p ≤ 3 →
        T ^ (4 : ℕ) ≤ ((N : ℝ) ^ h) ^ (p + 2) →
        (∀ n ∈ s, N < n ∧ n ≤ 2 * N) →
        (∑ n ∈ s, ‖coeff n‖ ^ 2) ≤ X ^ ε * N →
        (∫ t in Icc a (a + T),
          ‖verticalDirichlet152 s coeff σ t‖ ^ ((h : ℝ) * p)) ≤
          X ^ γ := by
  induction H with
  | zero =>
    refine ⟨1, by norm_num, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    refine ⟨hX, ?_⟩
    intro h hh hH
    omega
  | succ H ih =>
    obtain ⟨εprev, hεprev, hprev⟩ := ih
    obtain ⟨εnext, hεnext, hnext⟩ :=
      NormalizedPowerGrowth.eventually_bound (H + 1) (by omega) γ hγ
    refine ⟨min εprev εnext, lt_min hεprev hεnext, ?_⟩
    filter_upwards [hprev, hnext] with X hp hn
    refine ⟨hp.1, ?_⟩
    intro h hh hH s N coeff a T σ p hN hNX hT hTX hσ
      hplow hphigh hlength hs he
    by_cases hprevious : h ≤ H
    · have henergy : (∑ n ∈ s, ‖coeff n‖ ^ 2) ≤ X ^ εprev * N :=
        he.trans (mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le hp.1 (min_le_left εprev εnext))
          (Nat.cast_nonneg N))
      exact hp.2 h hh hprevious s N coeff a T σ p
        hN hNX hT hTX hσ hplow hphigh hlength hs henergy
    · have hequal : h = H + 1 := by omega
      subst h
      have henergy : (∑ n ∈ s, ‖coeff n‖ ^ 2) ≤ X ^ εnext * N :=
        he.trans (mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le hp.1 (min_le_right εprev εnext))
          (Nat.cast_nonneg N))
      exact hn.2 s N coeff a T σ p
        hN hNX hT hTX hσ hplow hphigh hlength hs henergy

end FinitePowerGrowth

#print axioms FinitePowerGrowth.eventually_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``FinitePowerGrowth.eventually_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "FINITE POWER GROWTH PASSED"
