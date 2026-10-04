import DifferenceParameters

/-!
Pure inverse-square companion to ReciprocalCancellation. The proof follows
that sibling's range and sign reductions, using the seed's square-phase
derivative bounds. No exponential-sum estimate is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators

namespace SquareCancellation
open Erdos374.ReciprocalPhaseShape152 Erdos374.HigherDifference152

def phaseRatioBound (r : ℕ) : ℝ := (4 : ℝ) ^ (r + 4)

theorem square_ratio_bound (r N : ℕ) (a : ℝ)
    (hN : 0 < N) (horder : r + 2 ≤ N)
    (ha : (N : ℝ) ≤ a) :
    squareRatio (r + 2) N a ≤ phaseRatioBound r := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have haPos : 0 < a := hNr.trans_le ha
  have horderR : ((r + 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast horder
  have hbase : a + (N : ℝ) + (r + 2 : ℕ) ≤ 4 * a := by linarith
  unfold squareRatio phaseRatioBound
  apply (div_le_iff₀ (pow_pos haPos _)).mpr
  have hh := pow_le_pow_left₀ (by positivity :
    0 ≤ a + (N : ℝ) + (r + 2 : ℕ)) hbase (r + 4)
  simpa only [mul_pow] using hh

theorem square_lower_range (r B N : ℕ) (a v : ℝ)
    (hN : 0 < N) (horder : r + 2 ≤ N)
    (hfactorial : (r + 3).factorial ≤ N)
    (ha : (N : ℝ) ≤ a) (haUpper : a ≤ 2 * (N : ℝ))
    (hlog : (4 : ℝ) ^ (r + 4) ≤ Real.log (N : ℝ))
    (hvLower : (N : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ (B + 1) ≤ |v|)
    (hvUpper : |v| ≤ (N : ℝ) ^ (r + 1)) :
    (Real.log (N : ℝ)) ^ B / (N : ℝ) ^ (r + 2) ≤
        squareLower (r + 2) N a v ∧
      squareLower (r + 2) N a v ≤ 1 / (N : ℝ) ^ 2 := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have haPos : 0 < a := hNr.trans_le ha
  have horderR : ((r + 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast horder
  have hbaseUpper : a + (N : ℝ) + (r + 2 : ℕ) ≤ 4 * (N : ℝ) := by
    linarith
  have hbaseLower : (N : ℝ) ≤ a + (N : ℝ) + (r + 2 : ℕ) := by
    linarith [Nat.cast_nonneg (α := ℝ) (r + 2)]
  have hfactorialR : ((r + 3).factorial : ℝ) ≤ N := by
    exact_mod_cast hfactorial
  have hfactorialOne : (1 : ℝ) ≤ (r + 3).factorial := by
    exact_mod_cast Nat.factorial_pos (r + 3)
  have hlogPos : 0 < Real.log (N : ℝ) :=
    lt_of_lt_of_le (by positivity) hlog
  have hv : 0 < |v| := lt_of_lt_of_le (by positivity) hvLower
  unfold squareLower
  constructor
  · calc
      _ = ((4 : ℝ) ^ (r + 4) * (N : ℝ) ^ 2 *
            (Real.log (N : ℝ)) ^ B) /
          (4 * (N : ℝ)) ^ (r + 4) := by
        simp only [mul_pow, pow_add]
        field_simp
      _ ≤ ((N : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ (B + 1)) /
          (4 * (N : ℝ)) ^ (r + 4) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        rw [pow_succ (Real.log (N : ℝ)) B]
        have hh := mul_le_mul_of_nonneg_right hlog
          (show 0 ≤ (N : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ B by positivity)
        nlinarith only [hh]
      _ ≤ |v| / (4 * (N : ℝ)) ^ (r + 4) :=
        div_le_div_of_nonneg_right hvLower (by positivity)
      _ ≤ ((r + 3).factorial : ℝ) * |v| /
          (4 * (N : ℝ)) ^ (r + 4) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) hbaseUpper (r + 4))
  · calc
      _ ≤ ((r + 3).factorial : ℝ) * |v| / (N : ℝ) ^ (r + 4) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ hNr.le hbaseLower (r + 4))
      _ ≤ (N : ℝ) * (N : ℝ) ^ (r + 1) / (N : ℝ) ^ (r + 4) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul hfactorialR hvUpper hv.le hNr.le
      _ = _ := by
        simp only [pow_add]
        field_simp

/-- Uniform cancellation for either sign of the inverse-square coefficient,
with constructed parameters and every prefix included. -/
theorem square_cancellation (r A : ℕ) :
    ∃ B cutoff : ℕ, ∀ N M : ℕ, cutoff ≤ N → M ≤ N →
      ∀ a v : ℝ, (N : ℝ) ≤ a → a ≤ 2 * (N : ℝ) →
        (N : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ B ≤ |v| →
        |v| ≤ (N : ℝ) ^ (r + 1) →
        ‖∑ n ∈ Finset.range M,
          Erdos374.KusminLandau151.e (sequencePhase a 0 v n)‖ ≤
            10 * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  have hC : 1 ≤ phaseRatioBound r := by
    exact one_le_pow₀ (by norm_num)
  obtain ⟨cutoff, hcutoff⟩ :=
    DifferenceParameters.cancellation_logarithmic_range r A (phaseRatioBound r) hC
  obtain ⟨logCutoff, hlogCutoff⟩ :=
    Erdos374.RemainingAnalytic115.RemainingAnalytic127.eventually_log_ge127
      ((4 : ℝ) ^ (r + 4))
  refine ⟨DifferenceParameters.logarithmicThresholdExponent r A + 1,
    max 1 (max cutoff (max logCutoff (max (r + 2) (r + 3).factorial))), ?_⟩
  intro N M hN hM a v ha haUpper hvLower hvUpper
  have hNpos : 0 < N := by omega
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have haPos : 0 < a := hNr.trans_le ha
  have hbounds := square_lower_range r
    (DifferenceParameters.logarithmicThresholdExponent r A) N a v
    hNpos (by omega) (by omega) ha haUpper
    (hlogCutoff N (by omega)) hvLower hvUpper
  have hratio := square_ratio_bound r N a hNpos (by omega) ha
  have hpositive : ∀ v : ℝ, 0 < v →
      (Real.log (N : ℝ)) ^ DifferenceParameters.logarithmicThresholdExponent r A /
          (N : ℝ) ^ (r + 2) ≤ squareLower (r + 2) N a v →
      squareLower (r + 2) N a v ≤ 1 / (N : ℝ) ^ 2 →
      ‖∑ n ∈ Finset.range M,
        Erdos374.KusminLandau151.e (sequencePhase a 0 v n)‖ ≤
          10 * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
    intro vp hvp hlowp hhighp
    let phase := sequencePhase a 0 ((-1 : ℝ) ^ (r + 2) * vp)
    have hL : 0 < squareLower (r + 2) N a vp := by
      unfold squareLower
      positivity
    have hdiff : ∀ n < M,
        squareLower (r + 2) N a vp ≤ difference (r + 2) phase n ∧
        difference (r + 2) phase n ≤
          phaseRatioBound r * squareLower (r + 2) N a vp := by
      intro n hn
      have hb := square_oriented_difference_bounds (r + 2) a vp haPos hvp.le
        N n (hn.trans_le hM)
      refine ⟨by simpa only [squareLower, abs_of_pos hvp] using hb.1, ?_⟩
      have hidentity : ((r + 3).factorial : ℝ) * vp / a ^ (r + 4) =
          squareRatio (r + 2) N a * squareLower (r + 2) N a vp := by
        unfold squareRatio squareLower
        rw [abs_of_pos hvp]
        field_simp
      exact hb.2.trans (hidentity ▸ mul_le_mul_of_nonneg_right hratio hL.le)
    have hmono := square_oriented_difference_antitone (r + 2) a vp haPos hvp.le
    have hsum := hcutoff N M (by omega) hM
      (squareLower (r + 2) N a vp) hlowp hhighp phase hdiff
      (Or.inr (fun _ _ _ _ h => hmono h))
    have he := norm_sum_sequencePhase_oriented (r + 2) a 0 vp M
    simp only [mul_zero] at he
    change ‖∑ n ∈ Finset.range M,
      Erdos374.KusminLandau151.e (sequencePhase a 0 ((-1 : ℝ) ^ (r + 2) * vp) n)‖ ≤
        10 * (N : ℝ) / Real.log (N : ℝ) ^ A at hsum
    rwa [he] at hsum
  have hlogPos : 0 < Real.log (N : ℝ) :=
    lt_of_lt_of_le (by positivity) (hlogCutoff N (by omega))
  have hvAbs : 0 < |v| := lt_of_lt_of_le (by positivity) hvLower
  by_cases hv : 0 ≤ v
  · have hvp : 0 < v := by rwa [abs_of_nonneg hv] at hvAbs
    exact hpositive v hvp hbounds.1 hbounds.2
  · have hvneg : v < 0 := lt_of_not_ge hv
    have hsum := hpositive (-v) (by linarith)
      (by simpa only [squareLower, abs_neg] using hbounds.1)
      (by simpa only [squareLower, abs_neg] using hbounds.2)
    have he := norm_sum_sequencePhase_neg a 0 v M
    simp only [neg_zero] at he
    rwa [he] at hsum

end SquareCancellation

#print axioms SquareCancellation.square_cancellation
run_cmd do
  let axioms ← Lean.collectAxioms ``SquareCancellation.square_cancellation
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "SQUARE CANCELLATION PASSED"
