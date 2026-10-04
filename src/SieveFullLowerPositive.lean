import SieveEventualStoppingBound
import SieveStoppingSharpOperator
import SieveStoppingPositiveBudget
import SieveFullCutoffTransfer

/-! Turn the eventual stopping envelope into a positive actual full-prime
lower selector at every logarithmic ratio at least 105/26. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real
namespace SieveFullLowerPositive
open SieveStoppingExpansion SieveStoppingRecurrence SieveStoppingTwoStep SieveEventualStoppingBound

theorem fullLower_eq_euler_sub_loss (T z : ℝ) :
    SieveFullCutoffTransfer.fullLower T z = primeEuler z-lowerLoss T z := by
  unfold SieveFullCutoffTransfer.fullLower lowerLoss primeEuler SievePrefixLoss.lower
  ring

theorem fourth_power_le_of_ratio (T z : ℝ) (hz : 2 ≤ z) (hT : z^2 ≤ T)
    (hr : (105/26:ℝ) ≤ log T/log z) : z^4 ≤ T := by
  have hz0 : 0 < z := by linarith
  have hT0 : 0 < T := (pow_pos hz0 2).trans_le hT
  have hlogz : 0 < log z := log_pos (by linarith)
  have hh := (le_div_iff₀ hlogz).mp (show (4:ℝ) ≤ log T/log z by linarith)
  apply (log_le_log_iff (pow_pos hz0 4) hT0).mp
  simpa only [log_pow, Nat.cast_ofNat] using hh

theorem eventual_loss_bound_of_envelope (henv : EventualEnvelope 91) :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^2 ≤ T →
      (105/26:ℝ) ≤ log T/log z → normalizedLower T z ≤ 49/50 := by
  obtain ⟨Y, hY, hb⟩ := henv
  let Z := max (SieveStoppingDecay.baseCutoff+2) (Y*SieveFiniteBase.saturationLevel Y)
  have hbase0 : 0 < SieveStoppingDecay.baseCutoff := exp_pos _
  have hZ2 : 2 ≤ Z := (by linarith : (2:ℝ) ≤ SieveStoppingDecay.baseCutoff+2).trans (le_max_left _ _)
  refine ⟨Z, hZ2, ?_⟩
  intro z T hz hT hr
  have hz2 : 2 ≤ z := hZ2.trans hz
  have hlarge : SieveStoppingDecay.baseCutoff < z := by
    have hh := (le_max_left _ _).trans hz
    linarith
  obtain ⟨hz64, hlog, _⟩ := SieveStoppingDecay.large_cutoff_conditions z hz2 hlarge
  have hchild : ∀ p ∈ SieveSmallWeights.pool z, ∀ q ∈ SieveSmallWeights.pool (p:ℝ),
      (q:ℝ)^3 < T/(p:ℝ) →
      normalizedLower ((T/(p:ℝ))/(q:ℝ)) (q:ℝ) ≤
        91*exp (-(log ((T/(p:ℝ))/(q:ℝ))/log (q:ℝ))) := by
    intro p hp q hq hg
    by_cases hqY : Y ≤ (q:ℝ)
    · exact hb (q:ℝ) ((T/(p:ℝ))/(q:ℝ)) hqY
        (SieveStoppingDecay.accepted_child_level T p q hq hg).2
    · rw [small_child_saturated T z Y p q hY ((le_max_right _ _).trans hz)
        hz2 hT hp hq (le_of_not_ge hqY)]
      positivity
  have ho := (SieveStoppingDecay.operator_bound_of_children T z 91 hchild).trans
    (mul_le_mul_of_nonneg_left
      (SieveStoppingSharpOperator.operator_exponential_majorant_small T z hz64 hT hlog)
      (by norm_num : (0:ℝ) ≤ 91))
  rw [normalizedLower_two_step, SieveStoppingForcing.forcing_eq_zero T z
    (fourth_power_le_of_ratio T z hz2 hT hr), zero_add]
  exact ho.trans (SieveStoppingPositiveBudget.normalized_loss_budget (log T/log z) hr)

theorem lower_bound_of_normalized_loss (T z : ℝ)
    (hloss : normalizedLower T z ≤ (49/50:ℝ)) :
    primeEuler z/50 ≤ SieveFullCutoffTransfer.fullLower T z := by
  have he := SieveEulerRatio.euler_pos z
  have hh := (div_le_iff₀ he).mp hloss
  rw [fullLower_eq_euler_sub_loss]
  linarith

theorem eventual_full_lower_of_envelope (henv : EventualEnvelope 91) :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^2 ≤ T →
      (105/26:ℝ) ≤ log T/log z →
        primeEuler z/50 ≤ SieveFullCutoffTransfer.fullLower T z := by
  obtain ⟨Z, hZ, hb⟩ := eventual_loss_bound_of_envelope henv
  exact ⟨Z, hZ, fun z T hz hT hr => lower_bound_of_normalized_loss T z (hb z T hz hT hr)⟩

theorem eventual_full_lower :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^2 ≤ T →
      (105/26:ℝ) ≤ log T/log z →
        primeEuler z/50 ≤ SieveFullCutoffTransfer.fullLower T z :=
  eventual_full_lower_of_envelope eventually_ninety_one

run_cmd do
  for decl in [``fullLower_eq_euler_sub_loss, ``fourth_power_le_of_ratio,
    ``eventual_loss_bound_of_envelope, ``lower_bound_of_normalized_loss,
    ``eventual_full_lower_of_envelope, ``eventual_full_lower] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "POSITIVE FULL LOWER SELECTOR FROM EVENTUAL STOPPING ENVELOPE"
end SieveFullLowerPositive
end
