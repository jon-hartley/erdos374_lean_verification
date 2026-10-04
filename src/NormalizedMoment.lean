import NormalizedMeanSquare
import LargeValueMoment

/-!
An explicit continuous moment bound for actual vertical Dirichlet
polynomials. All mean-square and large-value estimates are proved.
The supremum cover is an explicit finite amplitude parameter.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace NormalizedMoment
open Erdos374.HarmanGram152 DirichletLargeValueMeasure

theorem moment_bound (N lo hi : ℕ) (coeff : ℕ → ℂ)
    (a T A σ v p : ℝ) (J : ℕ)
    (hN : 1 ≤ N) (hlo : N ≤ lo) (hhi : hi ≤ 2 * N)
    (hT : 0 ≤ T) (hA : 0 < A) (hσ : 1 ≤ σ)
    (hv : 0 < v) (hp : 2 ≤ p) (hp6 : p ≤ 6)
    (henergy : (∑ n ∈ Finset.Ioc lo hi, ‖coeff n‖ ^ 2) ≤ A * N)
    (hcap : ∀ t ∈ Icc a (a + T),
      ‖verticalDirichlet152 (Finset.Ioc lo hi) coeff σ t‖ ≤ (2 : ℝ) ^ J * v) :
    (∫ t in Icc a (a + T), ‖verticalDirichlet152 (Finset.Ioc lo hi) coeff σ t‖ ^ p) ≤
      v ^ (p - 2) * (A * (T / N + 8 * (1 + Real.log (2 * N)))) +
        516 * J * (2 : ℝ) ^ p * (1 + Real.log (T + 1)) *
          (A * ((2 : ℝ) ^ J * v) ^ (p - 2) +
            (1024 ^ 2 * T * A ^ 3 * (1 + Real.log ((N : ℝ) + 1)) / (N : ℝ) ^ 2) *
              v ^ (p - 6)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs0 : ∀ n ∈ Finset.Ioc lo hi, 0 < n := by
    intro n hn
    have hh := (Finset.mem_Ioc.mp hn).1
    omega
  have hc := NormalizedMeanSquare.continuous_vertical (Finset.Ioc lo hi) coeff σ hs0
  have hGN : 0 ≤ 1 + Real.log ((N : ℝ) + 1) := by
    have hh := Real.log_nonneg (show 1 ≤ (N : ℝ) + 1 by
      linarith [Nat.cast_nonneg (α := ℝ) N])
    linarith
  have hGT : 0 ≤ 1 + Real.log (T + 1) := by
    have hh := Real.log_nonneg (show 1 ≤ T + 1 by linarith)
    linarith
  let K := 516 * (1 + Real.log (T + 1))
  let L := 1024 ^ 2 * T * A ^ 3 * (1 + Real.log ((N : ℝ) + 1)) / (N : ℝ) ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hlevel : ∀ w : ℝ, 0 < w →
      volume (levelSet (verticalDirichlet152 (Finset.Ioc lo hi) coeff σ) a T w) ≤
        ENNReal.ofReal ((K * A) / w ^ 2 + (K * L) / w ^ 6) := by
    intro w hw
    have hh := normalized_measure_bound N lo hi coeff a T A w σ hN hlo hhi hT hA hw hσ henergy
    convert hh using 1
    congr 1
    dsimp [K, L]
    field_simp
  have hh := LargeValueMoment.integral_bound
    (verticalDirichlet152 (Finset.Ioc lo hi) coeff σ) a T v p (K * A) (K * L) J
    hc hv hp hp6 (mul_nonneg hK hA.le) (mul_nonneg hK hL) hcap hlevel
  have hmean := NormalizedMeanSquare.mean_square_bound N lo hi coeff a T A σ
    hN hlo hhi hT hσ henergy
  apply hh.trans
  calc
    _ ≤ v ^ (p - 2) * (A * (T / N + 8 * (1 + Real.log (2 * N)))) +
        (J : ℝ) * (2 : ℝ) ^ p *
          ((K * A) * ((2 : ℝ) ^ J * v) ^ (p - 2) + (K * L) * v ^ (p - 6)) :=
      add_le_add (mul_le_mul_of_nonneg_left hmean (Real.rpow_nonneg hv.le _)) le_rfl
    _ = _ := by dsimp [K, L]; ring

end NormalizedMoment

#print axioms NormalizedMoment.moment_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``NormalizedMoment.moment_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "NORMALIZED MOMENT PASSED"
