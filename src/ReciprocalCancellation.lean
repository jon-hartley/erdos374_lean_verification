import DifferenceParameters

/-!
Actual reciprocal-phase cancellation from the constructed shift parameters.
This extends the seed's ReciprocalWindowPrefix152 argument. No prime-sum
estimate is assumed or proved here; this supplies its unweighted input.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators

namespace ReciprocalCancellation
open Erdos374.ReciprocalPhaseShape152 Erdos374.HigherDifference152

def phaseRatioBound (r : ℕ) : ℝ := 3 * (4 : ℝ) ^ (r + 3)

theorem reciprocal_ratio_bound (r N : ℕ) (a : ℝ)
    (hN : 0 < N) (horder : r + 2 ≤ N)
    (ha : (N : ℝ) ≤ a) :
    reciprocalRatio (r + 2) N a ≤ phaseRatioBound r := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have haPos : 0 < a := hNr.trans_le ha
  have horderR : ((r + 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast horder
  have hbase : a + (N : ℝ) + (r + 2 : ℕ) ≤ 4 * a := by linarith
  unfold reciprocalRatio phaseRatioBound
  apply (div_le_iff₀ (pow_pos haPos _)).mpr
  have hh := pow_le_pow_left₀ (by positivity :
    0 ≤ a + (N : ℝ) + (r + 2 : ℕ)) hbase (r + 3)
  rw [mul_pow] at hh
  nlinarith only [hh]

theorem reciprocal_lower_range (r B N : ℕ) (a u : ℝ)
    (hN : 0 < N) (horder : r + 2 ≤ N)
    (hfactorial : (r + 2).factorial ≤ N)
    (ha : (N : ℝ) ≤ a) (haUpper : a ≤ 2 * (N : ℝ))
    (hlog : 2 * (4 : ℝ) ^ (r + 3) ≤ Real.log (N : ℝ))
    (huLower : (N : ℝ) * (Real.log (N : ℝ)) ^ (B + 1) ≤ |u|)
    (huUpper : |u| ≤ (N : ℝ) ^ r) :
    (Real.log (N : ℝ)) ^ B / (N : ℝ) ^ (r + 2) ≤
        reciprocalLower (r + 2) N a u ∧
      reciprocalLower (r + 2) N a u ≤ 1 / (N : ℝ) ^ 2 := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have haPos : 0 < a := hNr.trans_le ha
  have horderR : ((r + 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast horder
  have hbaseUpper : a + (N : ℝ) + (r + 2 : ℕ) ≤ 4 * (N : ℝ) := by
    linarith
  have hbaseLower : (N : ℝ) ≤ a + (N : ℝ) + (r + 2 : ℕ) := by
    linarith [Nat.cast_nonneg (α := ℝ) (r + 2)]
  have hfactorialR : ((r + 2).factorial : ℝ) ≤ N := by
    exact_mod_cast hfactorial
  have hfactorialOne : (1 : ℝ) ≤ (r + 2).factorial := by
    exact_mod_cast Nat.factorial_pos (r + 2)
  have hlogPos : 0 < Real.log (N : ℝ) :=
    lt_of_lt_of_le (by positivity) hlog
  have hu : 0 < |u| := lt_of_lt_of_le (by positivity) huLower
  unfold reciprocalLower
  constructor
  · calc
      _ = (2 * (4 : ℝ) ^ (r + 3) * (N : ℝ) *
            (Real.log (N : ℝ)) ^ B) /
          (2 * (4 * (N : ℝ)) ^ (r + 3)) := by
        simp only [mul_pow, pow_add]
        field_simp
      _ ≤ ((N : ℝ) * (Real.log (N : ℝ)) ^ (B + 1)) /
          (2 * (4 * (N : ℝ)) ^ (r + 3)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        rw [pow_succ (Real.log (N : ℝ)) B]
        have hh := mul_le_mul_of_nonneg_right hlog
          (show 0 ≤ (N : ℝ) * (Real.log (N : ℝ)) ^ B by positivity)
        nlinarith only [hh]
      _ ≤ |u| / (2 * (4 * (N : ℝ)) ^ (r + 3)) :=
        div_le_div_of_nonneg_right huLower (by positivity)
      _ ≤ ((r + 2).factorial : ℝ) * |u| /
          (2 * (4 * (N : ℝ)) ^ (r + 3)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hbaseUpper (r + 3)) (by norm_num))
  · calc
      _ ≤ ((r + 2).factorial : ℝ) * |u| /
          (2 * (N : ℝ) ^ (r + 3)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hNr.le hbaseLower (r + 3)) (by norm_num))
      _ ≤ (N : ℝ) * (N : ℝ) ^ r / (2 * (N : ℝ) ^ (r + 3)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul hfactorialR huUpper hu.le hNr.le
      _ = 1 / (2 * (N : ℝ) ^ 2) := by
        simp only [pow_add]
        field_simp
      _ ≤ _ := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        nlinarith [sq_nonneg (N : ℝ)]

/-- Actual signed reciprocal phases, uniform in the starting point,
coefficients and every prefix. The logarithmic threshold and cutoff depend
only on r and A. The amplitude range is nonempty for r >= 2 eventually. -/
theorem reciprocal_cancellation (r A : ℕ) :
    ∃ B cutoff : ℕ, ∀ N M : ℕ, cutoff ≤ N → M ≤ N →
      ∀ a u v : ℝ, (N : ℝ) ≤ a → a ≤ 2 * (N : ℝ) →
        (N : ℝ) * (Real.log (N : ℝ)) ^ B ≤ |u| →
        |u| ≤ (N : ℝ) ^ r →
        2 * ((r + 3 : ℕ) : ℝ) * |v| ≤ |u| * a →
        ‖∑ n ∈ Finset.range M,
          Erdos374.KusminLandau151.e (sequencePhase a u v n)‖ ≤
            10 * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  have hC : 1 ≤ phaseRatioBound r := by
    unfold phaseRatioBound
    have hp : (1 : ℝ) ≤ 4 ^ (r + 3) := one_le_pow₀ (by norm_num)
    linarith
  obtain ⟨cutoff, hcutoff⟩ :=
    DifferenceParameters.cancellation_logarithmic_range r A (phaseRatioBound r) hC
  obtain ⟨logCutoff, hlogCutoff⟩ :=
    Erdos374.RemainingAnalytic115.RemainingAnalytic127.eventually_log_ge127
      (2 * (4 : ℝ) ^ (r + 3))
  refine ⟨DifferenceParameters.logarithmicThresholdExponent r A + 1,
    max 1 (max cutoff (max logCutoff (max (r + 2) (r + 2).factorial))), ?_⟩
  intro N M hN hM a u v ha haUpper huLower huUpper hdom
  have hNpos : 0 < N := by omega
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have haPos : 0 < a := hNr.trans_le ha
  have hbounds := reciprocal_lower_range r
    (DifferenceParameters.logarithmicThresholdExponent r A) N a u
    hNpos (by omega) (by omega) ha haUpper
    (hlogCutoff N (by omega)) huLower huUpper
  have hratio := reciprocal_ratio_bound r N a hNpos (by omega) ha
  have hpositive : ∀ u v : ℝ, 0 < u →
      2 * ((r + 3 : ℕ) : ℝ) * |v| ≤ u * a →
      (Real.log (N : ℝ)) ^ DifferenceParameters.logarithmicThresholdExponent r A /
          (N : ℝ) ^ (r + 2) ≤ reciprocalLower (r + 2) N a u →
      reciprocalLower (r + 2) N a u ≤ 1 / (N : ℝ) ^ 2 →
      ‖∑ n ∈ Finset.range M,
        Erdos374.KusminLandau151.e (sequencePhase a u v n)‖ ≤
          10 * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
    intro up vp hup hdomp hlowp hhighp
    let phase := sequencePhase a ((-1 : ℝ) ^ (r + 2) * up)
      ((-1 : ℝ) ^ (r + 2) * vp)
    have hL : 0 < reciprocalLower (r + 2) N a up := by
      unfold reciprocalLower
      positivity
    have hdiff : ∀ n < M,
        reciprocalLower (r + 2) N a up ≤ difference (r + 2) phase n ∧
        difference (r + 2) phase n ≤
          phaseRatioBound r * reciprocalLower (r + 2) N a up := by
      intro n hn
      have hb := oriented_difference_bounds (r + 2) a up vp haPos hup.le
        hdomp N n (hn.trans_le hM)
      refine ⟨by simpa only [reciprocalLower, abs_of_pos hup] using hb.1, ?_⟩
      have hidentity : 3 * ((r + 2).factorial : ℝ) * up /
          (2 * a ^ (r + 3)) =
          reciprocalRatio (r + 2) N a * reciprocalLower (r + 2) N a up := by
        unfold reciprocalRatio reciprocalLower
        rw [abs_of_pos hup]
        field_simp
      exact hb.2.trans (hidentity ▸ mul_le_mul_of_nonneg_right hratio hL.le)
    have hmono := oriented_difference_antitone (r + 2) a up vp
      haPos hup.le hdomp
    have hsum := hcutoff N M (by omega) hM
      (reciprocalLower (r + 2) N a up) hlowp hhighp phase hdiff
      (Or.inr (fun _ _ _ _ h => hmono h))
    simpa only [phase, norm_sum_sequencePhase_oriented] using hsum
  have hlogPos : 0 < Real.log (N : ℝ) :=
    lt_of_lt_of_le (by positivity) (hlogCutoff N (by omega))
  have huAbs : 0 < |u| := lt_of_lt_of_le (by positivity) huLower
  by_cases hu : 0 ≤ u
  · have hup : 0 < u := by rwa [abs_of_nonneg hu] at huAbs
    exact hpositive u v hup
      (by simpa only [abs_of_pos hup] using hdom) hbounds.1 hbounds.2
  · have huneg : u < 0 := lt_of_not_ge hu
    have hsum := hpositive (-u) (-v) (by linarith)
      (by simpa only [abs_neg, abs_of_neg huneg] using hdom)
      (by simpa only [reciprocalLower, abs_neg] using hbounds.1)
      (by simpa only [reciprocalLower, abs_neg] using hbounds.2)
    simpa only [norm_sum_sequencePhase_neg] using hsum

end ReciprocalCancellation

#print axioms ReciprocalCancellation.reciprocal_cancellation
run_cmd do
  let axioms ← Lean.collectAxioms
    ``ReciprocalCancellation.reciprocal_cancellation
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "RECIPROCAL CANCELLATION PASSED"
