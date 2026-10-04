import ReciprocalCancellation
import SquareCancellation

/-!
Use the proved cancellation estimates on integer intervals and on the exact
truncated correlations from Vaughan's identity. This extends the seed's
BilinearCancellation152, retaining its actual hyperbolic endpoints.

The correlation coefficient window is an explicit restriction. Near-diagonal
pairs can fail it and must be counted separately before a Type II sum is bounded.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators ComplexConjugate

namespace IntervalCancellation
open Erdos374.ReciprocalCharacter151 Erdos374.BilinearCorrelation152
open Erdos374.BilinearCancellation152 Erdos374.ReciprocalPhaseShape152

theorem interval_reciprocal_cancellation (r A : ℕ) :
    ∃ B cutoff : ℕ, ∀ N lo hi : ℕ, cutoff ≤ N →
      N ≤ lo → hi ≤ 2 * N → ∀ u v : ℝ,
        (N : ℝ) * Real.log (N : ℝ) ^ B ≤ |u| →
        |u| ≤ (N : ℝ) ^ r →
        2 * ((r + 3 : ℕ) : ℝ) * |v| ≤ |u| * N →
        ‖∑ d ∈ Finset.Ioc lo hi, character u v d‖ ≤
          10 * (N : ℝ) / Real.log (N : ℝ) ^ A := by
  obtain ⟨B, cutoff, hc⟩ := ReciprocalCancellation.reciprocal_cancellation r A
  refine ⟨B, max 2 cutoff, ?_⟩
  intro N lo hi hN hlo hhi u v huLower huUpper hdom
  have hNtwo : 2 ≤ N := by omega
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  by_cases hempty : hi ≤ lo
  · rw [Finset.Ioc_eq_empty_of_le hempty, Finset.sum_empty, norm_zero]
    positivity
  · have hloR : (N : ℝ) ≤ (lo : ℝ) + 1 := by exact_mod_cast (by omega : N ≤ lo + 1)
    have hhiR : (lo : ℝ) + 1 ≤ 2 * (N : ℝ) := by
      exact_mod_cast (by omega : lo + 1 ≤ 2 * N)
    rw [character_Ioc_eq]
    apply hc N (hi - lo) (by omega) (by omega) ((lo : ℝ) + 1) u v
      hloR hhiR huLower huUpper
    exact hdom.trans (mul_le_mul_of_nonneg_left hloR (abs_nonneg u))

theorem interval_square_cancellation (r A : ℕ) :
    ∃ B cutoff : ℕ, ∀ N lo hi : ℕ, cutoff ≤ N →
      N ≤ lo → hi ≤ 2 * N → ∀ v : ℝ,
        (N : ℝ) ^ 2 * Real.log (N : ℝ) ^ B ≤ |v| →
        |v| ≤ (N : ℝ) ^ (r + 1) →
        ‖∑ d ∈ Finset.Ioc lo hi, character 0 v d‖ ≤
          10 * (N : ℝ) / Real.log (N : ℝ) ^ A := by
  obtain ⟨B, cutoff, hc⟩ := SquareCancellation.square_cancellation r A
  refine ⟨B, max 2 cutoff, ?_⟩
  intro N lo hi hN hlo hhi v hvLower hvUpper
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  by_cases hempty : hi ≤ lo
  · rw [Finset.Ioc_eq_empty_of_le hempty, Finset.sum_empty, norm_zero]
    positivity
  · rw [character_Ioc_eq]
    apply hc N (hi - lo) (by omega) (by omega) ((lo : ℝ) + 1) v
      _ _ hvLower hvUpper
    · exact_mod_cast (by omega : N ≤ lo + 1)
    · exact_mod_cast (by omega : lo + 1 ≤ 2 * N)

/-- The actual Type II correlation with its original truncation. The lower
coefficient bound is deliberately retained; it need not hold near k=l. -/
theorem band_reciprocal_cancellation (r A : ℕ) :
    ∃ B cutoff : ℕ, ∀ D E P M k l : ℕ, cutoff ≤ D → E ≤ 2 * D →
      0 < k → 0 < l → ∀ u v : ℝ, u ≠ 0 →
        (D : ℝ) * Real.log (D : ℝ) ^ B ≤
          |u * (1 / (k : ℝ) - 1 / (l : ℝ))| →
        |u * (1 / (k : ℝ) - 1 / (l : ℝ))| ≤ (D : ℝ) ^ r →
        2 * ((r + 3 : ℕ) : ℝ) * (|v| / |u|) *
          (1 / (k : ℝ) + 1 / (l : ℝ)) ≤ (D : ℝ) →
        ‖∑ d ∈ Finset.Ioc D E,
          bandCharacter P M u v d k * conj (bandCharacter P M u v d l)‖ ≤
          10 * (D : ℝ) / Real.log (D : ℝ) ^ A := by
  obtain ⟨B, cutoff, hc⟩ := interval_reciprocal_cancellation r A
  refine ⟨B, cutoff, ?_⟩
  intro D E P M k l hD hE hk hl u v hu hlow hhigh hshape
  rw [interval_band_correlation D E P M k l u v hk hl]
  apply hc D (correlationLower D P k l) (correlationUpper E M k l)
    hD (le_max_left _ _) ((min_le_left _ _).trans hE) _ _ hlow hhigh
  exact typeII_dominance u v k l D (2 * ((r + 3 : ℕ) : ℝ)) hu
    (Nat.cast_pos.mpr hk) (Nat.cast_pos.mpr hl) hshape

theorem band_square_cancellation (r A : ℕ) :
    ∃ B cutoff : ℕ, ∀ D E P M k l : ℕ, cutoff ≤ D → E ≤ 2 * D →
      0 < k → 0 < l → ∀ v : ℝ,
        (D : ℝ) ^ 2 * Real.log (D : ℝ) ^ B ≤
          |v * (1 / (k : ℝ) ^ 2 - 1 / (l : ℝ) ^ 2)| →
        |v * (1 / (k : ℝ) ^ 2 - 1 / (l : ℝ) ^ 2)| ≤ (D : ℝ) ^ (r + 1) →
        ‖∑ d ∈ Finset.Ioc D E,
          bandCharacter P M 0 v d k * conj (bandCharacter P M 0 v d l)‖ ≤
          10 * (D : ℝ) / Real.log (D : ℝ) ^ A := by
  obtain ⟨B, cutoff, hc⟩ := interval_square_cancellation r A
  refine ⟨B, cutoff, ?_⟩
  intro D E P M k l hD hE hk hl v hlow hhigh
  rw [interval_band_correlation D E P M k l 0 v hk hl]
  simp only [zero_mul]
  exact hc D (correlationLower D P k l) (correlationUpper E M k l)
    hD (le_max_left _ _) ((min_le_left _ _).trans hE) _ hlow hhigh

end IntervalCancellation

#print axioms IntervalCancellation.band_reciprocal_cancellation
#print axioms IntervalCancellation.band_square_cancellation
run_cmd do
  for target in [``IntervalCancellation.band_reciprocal_cancellation,
      ``IntervalCancellation.band_square_cancellation] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "INTERVAL CANCELLATION PASSED"

run_cmd do
  for target in [``IntervalCancellation.interval_reciprocal_cancellation,
      ``IntervalCancellation.interval_square_cancellation,
      ``IntervalCancellation.band_reciprocal_cancellation,
      ``IntervalCancellation.band_square_cancellation] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "CHECKED SAMPLING PORT: ALL EXPORTED THEOREMS GUARDED"
