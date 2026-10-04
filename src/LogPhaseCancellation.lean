import LogPhaseShape
import PowerDifferenceParameters

/-!
Polynomial saving for actual logarithmic phases. The finite difference
scale is constructed from the amplitude; no derivative shape or auxiliary
window assumptions are left in the exported cancellation theorem.
Adapted from ReciprocalCancellation and the seed's all-order shape lemmas.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace LogPhaseCancellation
open Erdos374.HigherDifference152

def ratioBound (r : ℕ) : ℝ := (4 : ℝ) ^ (r + 2) * (r + 1).factorial

theorem difference_bounds (r N M : ℕ) (a u : ℝ)
    (hN : 0 < N) (horder : r + 2 ≤ N) (hM : M ≤ N)
    (ha : (N : ℝ) ≤ a) (haUpper : a ≤ 2 * (N : ℝ)) (hu : 0 ≤ u) :
    ∀ n < M,
      (u / (4 : ℝ) ^ (r + 2)) / (N : ℝ) ^ (r + 2) ≤
        difference (r + 2)
          (fun k => LogPhaseShape.phase ((-1 : ℝ) ^ (r + 1) * u) (a + k)) n ∧
      difference (r + 2)
          (fun k => LogPhaseShape.phase ((-1 : ℝ) ^ (r + 1) * u) (a + k)) n ≤
        ratioBound r * ((u / (4 : ℝ) ^ (r + 2)) / (N : ℝ) ^ (r + 2)) := by
  intro n hn
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hap : 0 < a := hNr.trans_le ha
  have horderR : ((r + 2 : ℕ) : ℝ) ≤ N := Nat.cast_le.mpr horder
  have hbase : a + (N : ℝ) + (r + 2 : ℕ) ≤ 4 * (N : ℝ) := by linarith
  have hfac : (1 : ℝ) ≤ (r + 1).factorial := by
    exact_mod_cast Nat.factorial_pos (r + 1)
  have hb := LogPhaseShape.oriented_difference_bounds (r + 1) N n a u
    hap hu (hn.trans_le hM)
  constructor
  · calc
      _ = u / (4 * (N : ℝ)) ^ (r + 2) := by rw [mul_pow]; ring
      _ ≤ ((r + 1).factorial : ℝ) * u / (4 * (N : ℝ)) ^ (r + 2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith
      _ ≤ ((r + 1).factorial : ℝ) * u /
          (a + (N : ℝ) + (r + 2 : ℕ)) ^ (r + 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ (by positivity) hbase _)
      _ ≤ _ := hb.1
  · calc
      _ ≤ ((r + 1).factorial : ℝ) * u / a ^ (r + 2) := hb.2
      _ ≤ ((r + 1).factorial : ℝ) * u / (N : ℝ) ^ (r + 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ hNr.le ha _)
      _ = _ := by unfold ratioBound; field_simp

/-- Uniform in the starting point, either amplitude sign, and every prefix.
For fixed r and theta, the saving exponent and cutoff are fixed too. -/
theorem logarithmic_cancellation (r : ℕ) (θ : ℝ)
    (hθ : 0 < θ) (hθone : θ ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ cutoff : ℕ, ∀ N M : ℕ,
      cutoff ≤ N → M ≤ N → ∀ a u : ℝ,
        (N : ℝ) ≤ a → a ≤ 2 * (N : ℝ) →
        (N : ℝ) ^ θ ≤ |u| → |u| ≤ (N : ℝ) ^ r →
        ‖∑ n ∈ Finset.range M,
          Erdos374.KusminLandau151.e (LogPhaseShape.phase u (a + n))‖ ≤
            10 * (N : ℝ) ^ (-δ) * (N : ℝ) := by
  let η : ℝ := θ / (4 * (r + 1 : ℕ))
  have hrp : (0 : ℝ) < (r + 1 : ℕ) := by positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hηhalf : η ≤ 1 / 2 := by
    dsimp [η]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (r + 1 : ℕ))).mpr
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) r]
  have hC : 1 ≤ ratioBound r := by
    have hp : (1 : ℝ) ≤ 4 ^ (r + 2) := one_le_pow₀ (by norm_num)
    have hf : (1 : ℝ) ≤ (r + 1).factorial := by
      exact_mod_cast Nat.factorial_pos (r + 1)
    exact one_le_mul_of_one_le_of_one_le hp hf
  obtain ⟨δ, hδ, cutoff, hcutoff⟩ :=
    PowerDifferenceParameters.cancellation_power_window r (ratioBound r) η hC hη hηhalf
  obtain ⟨constantCutoff, hconstant⟩ :=
    PowerDifferenceParameters.eventually_log_le_power ((4 : ℝ) ^ (r + 2))
      (θ / 2) (by positivity) (by positivity)
  refine ⟨δ, hδ, max (r + 2) (max cutoff constantCutoff), ?_⟩
  intro N M hN hM a u ha haUpper huLower huUpper
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlog : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hfour : (4 : ℝ) ^ (r + 2) ≤ (N : ℝ) ^ (θ / 2) := by
    have hh := hconstant N (by omega)
    have hp : 0 ≤ (4 : ℝ) ^ (r + 2) := by positivity
    nlinarith
  have hfourOne : (1 : ℝ) ≤ 4 ^ (r + 2) := one_le_pow₀ (by norm_num)
  have huAbs : 0 < |u| := (Real.rpow_pos_of_pos hNr θ).trans_le huLower
  let scale : ℝ := (|u| / (4 : ℝ) ^ (r + 2)) ^
    (1 / ((r + 1 : ℕ) : ℝ))
  have hs : 0 < scale := by
    dsimp [scale]
    exact Real.rpow_pos_of_pos
      (div_pos huAbs (by positivity : (0 : ℝ) < 4 ^ (r + 2))) _
  have hsPow : scale ^ (r + 1) = |u| / (4 : ℝ) ^ (r + 2) := by
    dsimp [scale]
    rw [← Real.rpow_mul_natCast (by positivity)]
    rw [one_div_mul_cancel (ne_of_gt hrp), Real.rpow_one]
  have hηid : η * (r + 1 : ℕ) = θ / 4 := by
    dsimp [η]
    field_simp
  have hsLower : (N : ℝ) ^ η ≤ scale := by
    apply (pow_le_pow_iff_left₀ (by positivity) hs.le (by omega : r + 1 ≠ 0)).mp
    rw [hsPow, ← Real.rpow_mul_natCast hNr.le, hηid]
    calc
      _ ≤ (N : ℝ) ^ (θ / 2) :=
        Real.rpow_le_rpow_of_exponent_le hNone (by linarith)
      _ ≤ |u| / (4 : ℝ) ^ (r + 2) := by
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 ^ (r + 2))).mpr
        calc
          _ ≤ (N : ℝ) ^ (θ / 2) * (N : ℝ) ^ (θ / 2) :=
            mul_le_mul_of_nonneg_left hfour (by positivity)
          _ = (N : ℝ) ^ θ := by rw [← Real.rpow_add hNr]; congr 1; ring
          _ ≤ _ := huLower
  have hsUpper : scale ≤ (N : ℝ) ^ (1 - η) := by
    apply (pow_le_pow_iff_left₀ hs.le (by positivity) (by omega : r + 1 ≠ 0)).mp
    rw [hsPow, ← Real.rpow_mul_natCast hNr.le]
    calc
      _ ≤ |u| := div_le_self huAbs.le hfourOne
      _ ≤ (N : ℝ) ^ r := huUpper
      _ = (N : ℝ) ^ (r : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hNone (by
        rw [sub_mul, one_mul, hηid]
        push_cast
        linarith)
  have hpositive : ∀ v : ℝ, 0 ≤ v → |u| = v →
      ‖∑ n ∈ Finset.range M,
        Erdos374.KusminLandau151.e (LogPhaseShape.phase v (a + n))‖ ≤
          10 * (N : ℝ) ^ (-δ) * (N : ℝ) := by
    intro v hv hvEq
    have hb := difference_bounds r N M a v hNpos (by omega) hM ha haUpper hv
    have hm := LogPhaseShape.oriented_difference_antitone (r + 1) a v
      (hNr.trans_le ha) hv
    have hh := hcutoff N M (by omega) hM scale hsLower hsUpper
      (fun k => LogPhaseShape.phase ((-1 : ℝ) ^ (r + 1) * v) (a + k))
      (by simpa only [hsPow, hvEq] using hb)
      (Or.inr (fun _ _ _ _ hij => hm hij))
    simpa only [LogPhaseShape.norm_sum_oriented] using hh
  by_cases hu : 0 ≤ u
  · exact hpositive u hu (abs_of_nonneg hu)
  · have hneg : u < 0 := lt_of_not_ge hu
    have hh := hpositive (-u) (by linarith) (abs_of_neg hneg)
    simpa only [LogPhaseShape.norm_sum_neg] using hh

end LogPhaseCancellation

#print axioms LogPhaseCancellation.logarithmic_cancellation
run_cmd do
  let axioms ← Lean.collectAxioms ``LogPhaseCancellation.logarithmic_cancellation
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "LOG PHASE CANCELLATION PASSED"
