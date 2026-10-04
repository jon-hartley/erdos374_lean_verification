import SieveStoppingDecay
import SieveStoppingUpperDecay
import SieveModelLoss

/-! Exponentially small relative stopping losses for both actual small-prime
sieve weights, at level D^s and cutoff D^(s^2). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real Set
namespace SieveSmallPrimeFundamental
open SieveStoppingExpansion SieveStoppingRecurrence

def decayConstant : ℝ := max SieveStoppingDecay.decayConstant
  SieveStoppingUpperDecay.upperDecayConstant

theorem decayConstant_pos : 0 < decayConstant :=
  SieveStoppingDecay.decayConstant_pos.trans_le (le_max_left _ _)

theorem scale_square_le (D s : ℝ) (hD : 1 < D) (hs : 0 < s) (hsHalf : s ≤ 1/2) :
    (D^(s^2))^2 ≤ D^s := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ D)]
  apply Real.rpow_le_rpow_of_exponent_le hD.le
  norm_num
  nlinarith [mul_nonneg hs.le (show 0 ≤ 1/2-s by linarith)]

theorem scale_le (D s : ℝ) (hD : 1 < D) (hs : 0 < s) (hsHalf : s ≤ 1/2) :
    D^(s^2) ≤ D^s := by
  apply Real.rpow_le_rpow_of_exponent_le hD.le
  nlinarith [mul_nonneg hs.le (show 0 ≤ 1/2-s by linarith)]

theorem logarithmic_parameter (D s : ℝ) (hD : 1 < D) (hs : 0 < s) :
    log (D^s) / log (D^(s^2)) = 1/s := by
  have hD0 : 0 < D := by linarith
  have hl : log D ≠ 0 := (log_pos hD).ne'
  rw [Real.log_rpow hD0, Real.log_rpow hD0]
  field_simp

theorem loss_lower_eq (D s : ℝ) : SieveModelLoss.loss D s false = lowerLoss (D^s) (D^(s^2)) := by
  symm
  exact lower_expansion (SieveRosser.cubicGate (D^s)) 1
    (SieveSmallWeights.primes (D^(s^2))) (fun p => (p:ℝ)⁻¹)
    (SieveSmallWeights.primes_nodup _)

theorem loss_upper_eq (D s : ℝ) : SieveModelLoss.loss D s true = upperLoss (D^s) (D^(s^2)) := by
  symm
  exact upper_expansion (SieveRosser.cubicGate (D^s)) 1
    (SieveSmallWeights.primes (D^(s^2))) (fun p => (p:ℝ)⁻¹)
    (SieveSmallWeights.primes_nodup _)

theorem primes_nil_of_le_two (z : ℝ) (hz : z ≤ 2) : SieveSmallWeights.primes z = [] := by
  have hp : SieveSmallWeights.pool z = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hpp, hpl⟩ := (SieveSmallWeights.mem_pool z p).mp hp
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hpp.two_le
    linarith
  simp [SieveSmallWeights.primes, hp]

theorem loss_zero_of_small_cutoff (D s : ℝ) (hu : D^(s^2) ≤ 2) (mode : Bool) :
    SieveModelLoss.loss D s mode = 0 := by
  unfold SieveModelLoss.loss
  rw [primes_nil_of_le_two _ hu]
  simp [SieveStoppingExpansion.stops]

theorem relative_loss_bound (D s : ℝ) (mode : Bool) (hD : 1 < D)
    (hs : 0 < s) (hsHalf : s ≤ 1/2) :
    SieveModelLoss.loss D s mode ≤
      decayConstant * exp (-1/s) * SieveModelLoss.euler D s := by
  by_cases hu : 2 ≤ D^(s^2)
  · cases mode
    · rw [loss_lower_eq]
      have h := SieveStoppingDecay.normalizedLower_bound (D^s) (D^(s^2)) hu
        (scale_square_le D s hD hs hsHalf)
      change lowerLoss (D^s) (D^(s^2)) / primeEuler (D^(s^2)) ≤ _ at h
      rw [logarithmic_parameter D s hD hs] at h
      have he : SieveStoppingDecay.decayConstant * exp (-(1/s)) ≤ decayConstant * exp (-1/s) := by
        rw [neg_div]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (exp_pos _).le
      exact (div_le_iff₀ (SieveEulerRatio.euler_pos _)).mp (h.trans he)
    · rw [loss_upper_eq]
      have h := SieveStoppingUpperDecay.normalizedUpper_bound (D^s) (D^(s^2)) hu
        (scale_le D s hD hs hsHalf)
      rw [logarithmic_parameter D s hD hs] at h
      have he : SieveStoppingUpperDecay.upperDecayConstant * exp (-(1/s)) ≤
          decayConstant * exp (-1/s) := by
        rw [neg_div]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (exp_pos _).le
      exact (div_le_iff₀ (SieveEulerRatio.euler_pos _)).mp (h.trans he)
  · rw [loss_zero_of_small_cutoff D s (le_of_not_ge hu) mode]
    exact mul_nonneg (mul_nonneg decayConstant_pos.le (exp_pos _).le) (SieveModelLoss.euler_pos _ _).le

theorem exponential_budget_small (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ →
      decayConstant * exp (-1/s) ≤ ε := by
  let L := |log (ε/decayConstant)|+1
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨min (1/2) (1/L), lt_min (by norm_num) (div_pos (by norm_num) hL),
    min_le_left _ _, ?_⟩
  intro s hs hss
  have hsL : s ≤ 1/L := hss.trans (min_le_right _ _)
  have hLs : L ≤ 1/s := by
    apply (le_div_iff₀ hs).mpr
    have h := (le_div_iff₀ hL).mp hsL
    nlinarith
  have hlog : -1/s ≤ log (ε/decayConstant) := by
    have h := neg_abs_le (log (ε/decayConstant))
    dsimp [L] at hLs
    rw [neg_div]
    linarith
  calc
    _ ≤ decayConstant * exp (log (ε/decayConstant)) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr hlog) decayConstant_pos.le
    _ = ε := by
      rw [exp_log (div_pos hε decayConstant_pos)]
      field_simp [decayConstant_pos.ne']

theorem uniformly_small_relative_loss (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ →
      ∀ D : ℝ, 1 < D → ∀ mode : Bool,
        SieveModelLoss.loss D s mode ≤ ε * SieveModelLoss.euler D s := by
  obtain ⟨s₀, hs₀, hsHalf, hb⟩ := exponential_budget_small ε hε
  refine ⟨s₀, hs₀, hsHalf, ?_⟩
  intro s hs hss D hD mode
  exact (relative_loss_bound D s mode hD hs (hss.trans hsHalf)).trans
    (mul_le_mul_of_nonneg_right (hb s hs hss) (SieveModelLoss.euler_pos _ _).le)

run_cmd do
  for decl in [``decayConstant_pos, ``scale_square_le, ``scale_le, ``logarithmic_parameter,
    ``loss_lower_eq, ``loss_upper_eq, ``primes_nil_of_le_two, ``loss_zero_of_small_cutoff,
    ``relative_loss_bound, ``exponential_budget_small, ``uniformly_small_relative_loss] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL SMALL-PRIME FUNDAMENTAL LOSS BOUND PASSED"
end SieveSmallPrimeFundamental
end
