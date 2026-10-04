import NormalizedPowerMoment
import FlatPowerCap

/-!
An eighth-moment bound for the actual flat polynomial. The supremum
condition is discharged by the proved log-phase power saving.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace FlatEighthMoment
open Erdos374.HarmanGram152 NormalizedPowerLevel DyadicLevelParameters
open SupremumMoment MomentThreshold

def meanSix (C : ℝ) (N : ℕ) (T ε : ℝ) : ℝ :=
  C * (2 * (N : ℝ)) ^ ε *
    (T / (N : ℝ) ^ 3 + 32 * (1 + 3 * Real.log (2 * N)))

def upperBound (D C : ℝ) (N : ℕ) (T ε X κ : ℝ) : ℝ :=
  let E := energyBudget D N 3 ε 1
  let Q := quadratic (N ^ 3) 3 T E
  let B := sextic (N ^ 3) 3 T E
  (B / X ^ (-κ)) ^ (1 / 5 : ℝ) * meanSix C N T ε +
    bandCountBound (cutoff B (X ^ (-κ)) (8 / 3)) (X ^ (-3 * κ)) *
      (2 : ℝ) ^ (8 / 3 : ℝ) * (Q * (2 : ℝ) ^ (2 / 3 : ℝ) + 1) * X ^ (-κ)

theorem eventually_bound (η ρ : ℝ) (hη : 0 < η) (hρ : 0 < ρ) (hρone : ρ ≤ 1) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ η ∧ ∃ D : ℝ, 0 < D ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧ ∀ (N lo hi : ℕ) (a T σ : ℝ),
        X ^ η ≤ (N : ℝ) → (N : ℝ) ≤ X → N ≤ lo → hi ≤ 2 * N →
        0 < T → 1 ≤ σ → (∀ t ∈ Icc a (a + T), X ^ ρ ≤ |t| ∧ |t| ≤ X) →
        (∫ t in Icc a (a + T),
          ‖verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t‖ ^ (8 : ℕ)) ≤
            upperBound D C N T (κ / 100) X κ := by
  obtain ⟨κ, hκ, hκη, hcap⟩ := FlatPowerCap.eventually_bound η ρ η hη hρ hρone hη
  obtain ⟨D, hD, C, hC, hmoment⟩ := NormalizedPowerMoment.integral_bound 3 (by norm_num)
    (κ / 100) (by positivity)
  refine ⟨κ, hκ, hκη, D, hD, C, hC, ?_⟩
  filter_upwards [hcap] with X hX
  refine ⟨hX.1, ?_⟩
  intro N lo hi a T σ hNlower hNupper hlo hhi hT hσ htimes
  have hXp : 0 < X := by linarith [hX.1]
  have hN : 1 ≤ N := by
    have hh := (Real.one_le_rpow hX.1 hη.le).trans hNlower
    exact_mod_cast hh
  have hs : ∀ n ∈ Finset.Ioc lo hi, N < n ∧ n ≤ 2 * N := by
    intro n hn
    have hh := Finset.mem_Ioc.mp hn
    omega
  have henergy : (∑ n ∈ Finset.Ioc lo hi, ‖(1 : ℂ)‖ ^ 2) ≤ (1 : ℝ) * N := by
    simp only [norm_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
      Nat.card_Ioc, one_mul]
    exact_mod_cast (show hi - lo ≤ N by omega)
  have hU : 0 ≤ X ^ (-3 * κ) := Real.rpow_nonneg hXp.le _
  have hμ : 0 < X ^ (-κ) := Real.rpow_pos_of_pos hXp _
  have hpoint : ∀ t ∈ Icc a (a + T),
      ‖verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t‖ ^ 3 ≤ X ^ (-3 * κ) := by
    intro t ht
    have hh := pow_le_pow_left₀ (norm_nonneg _)
      (hX.2 N lo hi hNlower hNupper hlo hhi t σ (htimes t ht).1 (htimes t ht).2 hσ) 3
    convert hh using 1
    rw [← Real.rpow_mul_natCast hXp.le]
    congr 1
    norm_num
    ring
  have hpower : (X ^ (-3 * κ)) ^ ((8 / 3 : ℝ) - 2) ≤ X ^ (-κ) := by
    rw [← Real.rpow_mul hXp.le]
    apply Real.rpow_le_rpow_of_exponent_le hX.1
    nlinarith
  have hh := hmoment (Finset.Ioc lo hi) N (fun _ => 1) a T 1 σ
    (X ^ (-3 * κ)) (8 / 3) (X ^ (-κ)) hN hT (by norm_num) hσ hU
    (by norm_num) (by norm_num) hμ hs henergy hpoint hpower
  dsimp only at hh
  norm_num only [show (3 : ℝ) * (8 / 3) = 8 by norm_num,
    Real.rpow_natCast, one_pow, mul_one, Nat.cast_ofNat,
    show (8 / 3 : ℝ) - 2 = 2 / 3 by norm_num,
    show (6 : ℝ) - 8 / 3 = 10 / 3 by norm_num,
    show (2 / 3 : ℝ) / (10 / 3) = 1 / 5 by norm_num] at hh
  convert hh using 1
  · norm_cast
  · unfold upperBound meanSix
    norm_num

end FlatEighthMoment

#print axioms FlatEighthMoment.eventually_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``FlatEighthMoment.eventually_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "FLAT EIGHTH MOMENT PASSED"
