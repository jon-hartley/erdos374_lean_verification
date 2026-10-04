import NormalizedMoment
import DyadicAmplitudeCover

/-!
Remove the free amplitude-cover parameter from the continuous moment
estimates. The price is an explicit logarithm of the amplitude ratio.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace SupremumMoment
open DirichletLargeValueMeasure Erdos374.HarmanGram152

def bandCountBound (v U : ℝ) : ℝ :=
  1 + Real.log (max (U / v) 1) / Real.log 2

theorem bandCountBound_nonneg (v U : ℝ) : 0 ≤ bandCountBound v U := by
  have hh := Real.log_nonneg (le_max_right (U / v) 1)
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  dsimp [bandCountBound]
  positivity

theorem integral_bound (F : ℝ → ℂ) (a T v U p A B : ℝ)
    (hF : Continuous F) (hv : 0 < v) (hp : 2 ≤ p) (hp6 : p ≤ 6)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcap : ∀ t ∈ Icc a (a + T), ‖F t‖ ≤ U)
    (hlevel : ∀ w : ℝ, 0 < w → volume (levelSet F a T w) ≤
      ENNReal.ofReal (A / w ^ 2 + B / w ^ 6)) :
    (∫ t in Icc a (a + T), ‖F t‖ ^ p) ≤
      v ^ (p - 2) * (∫ t in Icc a (a + T), ‖F t‖ ^ 2) +
        bandCountBound v U * (2 : ℝ) ^ p *
          (A * (2 * max U v) ^ (p - 2) + B * v ^ (p - 6)) := by
  obtain ⟨J, hJcover, hJheight, hJcount⟩ :=
    DyadicAmplitudeCover.exists_cover v U hv
  have hh := LargeValueMoment.integral_bound F a T v p A B J
    hF hv hp hp6 hA hB (fun t ht => (hcap t ht).trans hJcover) hlevel
  apply hh.trans
  apply add_le_add le_rfl
  have hheight : ((2 : ℝ) ^ J * v) ^ (p - 2) ≤
      (2 * max U v) ^ (p - 2) :=
    Real.rpow_le_rpow (by positivity) hJheight (by linarith)
  have hterms := add_le_add_right
    (mul_le_mul_of_nonneg_left hheight hA) (B * v ^ (p - 6))
  have hfactor : (J : ℝ) * (2 : ℝ) ^ p ≤
      bandCountBound v U * (2 : ℝ) ^ p :=
    mul_le_mul_of_nonneg_right hJcount (by positivity)
  exact mul_le_mul hfactor (by simpa only [add_comm] using hterms) (by positivity) (by
    exact mul_nonneg (bandCountBound_nonneg v U) (by positivity))

theorem normalized_bound (N lo hi : ℕ) (coeff : ℕ → ℂ)
    (a T A σ v U p : ℝ)
    (hN : 1 ≤ N) (hlo : N ≤ lo) (hhi : hi ≤ 2 * N)
    (hT : 0 ≤ T) (hA : 0 < A) (hσ : 1 ≤ σ)
    (hv : 0 < v) (hp : 2 ≤ p) (hp6 : p ≤ 6)
    (henergy : (∑ n ∈ Finset.Ioc lo hi, ‖coeff n‖ ^ 2) ≤ A * N)
    (hcap : ∀ t ∈ Icc a (a + T),
      ‖verticalDirichlet152 (Finset.Ioc lo hi) coeff σ t‖ ≤ U) :
    (∫ t in Icc a (a + T), ‖verticalDirichlet152 (Finset.Ioc lo hi) coeff σ t‖ ^ p) ≤
      v ^ (p - 2) * (A * (T / N + 8 * (1 + Real.log (2 * N)))) +
        516 * bandCountBound v U * (2 : ℝ) ^ p * (1 + Real.log (T + 1)) *
          (A * (2 * max U v) ^ (p - 2) +
            (1024 ^ 2 * T * A ^ 3 * (1 + Real.log ((N : ℝ) + 1)) / (N : ℝ) ^ 2) *
              v ^ (p - 6)) := by
  obtain ⟨J, hJcover, hJheight, hJcount⟩ :=
    DyadicAmplitudeCover.exists_cover v U hv
  have hh := NormalizedMoment.moment_bound N lo hi coeff a T A σ v p J
    hN hlo hhi hT hA hσ hv hp hp6 henergy
    (fun t ht => (hcap t ht).trans hJcover)
  have hGN : 0 ≤ 1 + Real.log ((N : ℝ) + 1) := by
    have hh := Real.log_nonneg (show 1 ≤ (N : ℝ) + 1 by
      linarith [Nat.cast_nonneg (α := ℝ) N])
    linarith
  have hGT : 0 ≤ 1 + Real.log (T + 1) := by
    have hh := Real.log_nonneg (show 1 ≤ T + 1 by linarith)
    linarith
  apply hh.trans
  apply add_le_add le_rfl
  have hheight := Real.rpow_le_rpow (by positivity : 0 ≤ (2 : ℝ) ^ J * v)
    hJheight (show 0 ≤ p - 2 by linarith)
  have hterms := add_le_add_right (mul_le_mul_of_nonneg_left hheight hA.le)
    ((1024 ^ 2 * T * A ^ 3 * (1 + Real.log ((N : ℝ) + 1)) / (N : ℝ) ^ 2) *
      v ^ (p - 6))
  have hfactor : 516 * (J : ℝ) * (2 : ℝ) ^ p * (1 + Real.log (T + 1)) ≤
      516 * bandCountBound v U * (2 : ℝ) ^ p * (1 + Real.log (T + 1)) := by
    gcongr
    exact hJcount
  exact mul_le_mul hfactor (by simpa only [add_comm] using hterms) (by positivity) (by
    have := bandCountBound_nonneg v U
    positivity)

end SupremumMoment

#print axioms SupremumMoment.normalized_bound
run_cmd do
  for decl in [``SupremumMoment.integral_bound, ``SupremumMoment.normalized_bound] do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "SUPREMUM MOMENT PASSED"
