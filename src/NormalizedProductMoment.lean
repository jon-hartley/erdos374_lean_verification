import NormalizedProductMeanSquare
import MomentThreshold

/-!
Intermediate moments of the actual mixed product. Both its large-value
measure and mean square are proved. The full-product supremum remains
an explicit hypothesis here and is discharged in the flat application.
This follows the existing NormalizedPowerMoment assembly.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace NormalizedProductMoment
open Erdos374.HarmanGram152 DirichletLargeValueMeasure DyadicLevelParameters
open NormalizedProductLevel SupremumMoment MomentThreshold

theorem integral_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (K M : ℕ) (leftSupport rightSupport : Finset ℕ)
        (left right : ℕ → ℂ) (a T A B σ U p μ : ℝ),
      1 ≤ K → 1 ≤ M → 0 < T → 0 < A → 0 < B → 1 ≤ σ →
      0 ≤ U → 2 ≤ p → p < 6 → 0 < μ →
      (∀ n ∈ leftSupport, K < n ∧ n ≤ 2 * K) →
      (∀ n ∈ rightSupport, M < n ∧ n ≤ 2 * M) →
      (∑ n ∈ leftSupport, ‖left n‖ ^ 2) ≤ A * K →
      (∑ n ∈ rightSupport, ‖right n‖ ^ 2) ≤ B * M →
      (∀ t ∈ Icc a (a + T),
        ‖verticalDirichlet152 leftSupport left σ t *
          verticalDirichlet152 rightSupport right σ t‖ ≤ U) →
      U ^ (p - 2) ≤ μ →
      let E := energyBudget D K M ε A B
      let Q := quadratic (K * M) 2 T E
      let V := sextic (K * M) 2 T E
      (∫ t in Icc a (a + T),
        ‖verticalDirichlet152 leftSupport left σ t *
          verticalDirichlet152 rightSupport right σ t‖ ^ p) ≤
        (V / μ) ^ ((p - 2) / (6 - p)) *
          ((T + 4 * (4 * K * M : ℕ) *
            (1 + Real.log (4 * K * M : ℕ))) * energyBudget C K M ε A B) +
        bandCountBound (cutoff V μ p) U * (2 : ℝ) ^ p *
          (Q * (2 : ℝ) ^ (p - 2) + 1) * μ := by
  obtain ⟨D, hD, hlevel⟩ := NormalizedProductLevel.measure_bound ε hε
  obtain ⟨C, hC, hmean⟩ := NormalizedProductMeanSquare.integral_bound ε hε
  refine ⟨D, hD, C, hC, ?_⟩
  intro K M leftSupport rightSupport left right a T A B σ U p μ
    hK hM hT hA hB hσ hU hp hp6 hμ hsK hsM heK heM hcap hpower
  let F := fun t => verticalDirichlet152 leftSupport left σ t *
    verticalDirichlet152 rightSupport right σ t
  let E := energyBudget D K M ε A B
  let Q := quadratic (K * M) 2 T E
  let V := sextic (K * M) 2 T E
  have hFc : Continuous F :=
    (NormalizedMeanSquare.continuous_vertical leftSupport left σ (by
      intro n hn
      have hh := (hsK n hn).1
      omega)).mul
    (NormalizedMeanSquare.continuous_vertical rightSupport right σ (by
      intro n hn
      have hh := (hsM n hn).1
      omega))
  have hKp : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hEp : 0 < E := by dsimp [E, energyBudget]; positivity
  have hQ : 0 ≤ Q := quadratic_nonnegative _ _ _ _ hT.le hEp.le
  have hV : 0 < V := sextic_positive _ _ _ _ (by nlinarith) (by norm_num) hT hEp
  have hl : ∀ w : ℝ, 0 < w → volume (levelSet F a T w) ≤
      ENNReal.ofReal (Q / w ^ 2 + V / w ^ 6) := by
    intro w hw
    exact hlevel K M leftSupport rightSupport left right a T A B σ w
      hK hM hT.le hA hB hσ hw hsK hsM heK heM
  have hh := MomentThreshold.integral_bound F a T U p Q V μ
    hFc hU hp hp6 hQ hV hμ hcap hpower hl
  have hm := hmean K M leftSupport rightSupport left right a T A B σ
    hK hM hT.le hA hB hσ hsK hsM heK heM
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hm
    (Real.rpow_nonneg (div_pos hV hμ).le _)) le_rfl)

end NormalizedProductMoment

#print axioms NormalizedProductMoment.integral_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``NormalizedProductMoment.integral_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "NORMALIZED PRODUCT MOMENT PASSED"
