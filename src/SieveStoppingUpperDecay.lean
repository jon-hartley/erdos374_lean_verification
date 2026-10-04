import SieveStoppingDecay
import PrimeEulerAcceptedMajorant

/-! The upper selector loss splits into the actual accepted lower losses and
the rejected first-prime mass. The latter has compact logarithmic support. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SieveStoppingUpperDecay
open SieveStoppingExpansion SieveStoppingRecurrence SieveStoppingTwoStep
open SieveStoppingForcing PrimeEulerLogBounds PrimeEulerAcceptedInner

def rejectedMass (T z : ℝ) : ℝ :=
  ∑ p ∈ SieveSmallWeights.pool z,
    if (p:ℝ)^3 < T then 0 else PrimeEulerMass.weight p / primeEuler z

theorem rejectedMass_eq_zero (T z : ℝ) (hT : z^3 ≤ T) : rejectedMass T z = 0 := by
  unfold rejectedMass
  apply Finset.sum_eq_zero
  intro p hp
  obtain ⟨_, hpz⟩ := (SieveSmallWeights.mem_pool z p).mp hp
  have hg : (p:ℝ)^3 < T :=
    (pow_lt_pow_left₀ hpz (Nat.cast_nonneg p) (by decide : 3 ≠ 0)).trans_le hT
  simp only [hg, ite_true]

theorem rejectedMass_le_interval (T z : ℝ) (hz : 0 < z) (hT : z ≤ T) :
    rejectedMass T z ≤ ∑ p ∈ intervalPrimes (root z 3) z,
      PrimeEulerMass.weight p / primeEuler z := by
  rw [interval_eq_filter, Finset.sum_filter]
  unfold rejectedMass
  apply Finset.sum_le_sum
  intro p hp
  have hpp := ((SieveSmallWeights.mem_pool z p).mp hp).1
  have hp0 : (0:ℝ) < p := by exact_mod_cast hpp.pos
  by_cases hg : (p:ℝ)^3 < T
  · simp only [hg, ite_true]
    split_ifs
    · exact normalized_weight_nonneg p z
    · exact le_rfl
  · have hs : root z 3 ≤ (p:ℝ) := by
      by_contra hn
      have hplt : (p:ℝ) < Real.exp (Real.log z/3) := lt_of_not_ge hn
      have hp3 := (cube_lt_iff_lt_exp z (p:ℝ) hz hp0).mpr hplt
      linarith
    simp only [hg, hs, ite_false, ite_true, le_refl]

theorem rejectedMass_bound (T z : ℝ) (hz : 64 ≤ z) (hT : z ≤ T) :
    rejectedMass T z ≤ 2+9*epsilon z := by
  have hlog : Real.log z ≠ 0 := (Real.log_pos (by linarith)).ne'
  have ha : 2 ≤ root z 3 := root_lower 2 z 3 (by norm_num) (by norm_num) (by nlinarith)
  have hab := root_le_self z 3 (by linarith) (by norm_num)
  apply (rejectedMass_le_interval T z (by linarith) hT).trans
  apply (PrimeEulerMass.normalized_interval_bound _ _ ha hab).trans_eq
  simp only [root, Real.log_exp, Nat.cast_ofNat, epsilon]
  field_simp
  ring

theorem rejectedMass_exponential (T z : ℝ) (hz : 64 ≤ z) (hT : z ≤ T)
    (he : epsilon z ≤ 1) :
    rejectedMass T z ≤ (11*Real.exp 3)*Real.exp (-(Real.log T/Real.log z)) := by
  by_cases hf : z^3 ≤ T
  · rw [rejectedMass_eq_zero T z hf]
    positivity
  · have hT0 : 0 < T := by linarith
    have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
    have hlog := Real.log_lt_log hT0 (lt_of_not_ge hf)
    simp only [Real.log_pow, Nat.cast_ofNat] at hlog
    have hr : Real.log T/Real.log z < 3 := (div_lt_iff₀ hlogz).mpr (by linarith)
    have hb : rejectedMass T z ≤ 11 := by linarith [rejectedMass_bound T z hz hT]
    apply hb.trans
    rw [mul_assoc, ← Real.exp_add]
    have hm : 1 ≤ Real.exp (3 + -(Real.log T/Real.log z)) := by
      calc
        (1:ℝ) = Real.exp 0 := by simp
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    nlinarith

theorem acceptedMass_bound (T z : ℝ) (hz : 2 ≤ z) (hT : z ≤ T)
    (he : epsilon z ≤ 1) :
    acceptedExponentialMass T z ≤ (72*Real.exp 1)*Real.exp (-(Real.log T/Real.log z)) := by
  have he0 : 0 ≤ epsilon z := div_nonneg PrimeEulerDimensionOne.errorConstant_pos.le
    (Real.log_pos (by linarith)).le
  have he2 : (epsilon z)^2 ≤ 1 := by simpa using pow_le_pow_left₀ he0 he 2
  have hi := RosserInnerIntegral.inner_le_exp (PrimeEulerAcceptedParameters.parameter T z)
    (PrimeEulerAcceptedParameters.parameter_ge_one T z hz hT)
  have hb := PrimeEulerAcceptedMajorant.accepted_exponential_majorant T z hz hT
  change acceptedExponentialMass T z ≤ _ at hb
  change RosserInnerIntegral.inner (Real.log T/Real.log z) ≤
    Real.exp 1*Real.exp (-(Real.log T/Real.log z)) at hi
  change acceptedExponentialMass T z ≤ RosserInnerIntegral.inner (Real.log T/Real.log z) +
    20*Real.exp 1*(epsilon z)*Real.exp (-(Real.log T/Real.log z)) +
    51*Real.exp 1*(epsilon z)^2*Real.exp (-(Real.log T/Real.log z)) at hb
  have hA := mul_le_mul_of_nonneg_right he
    (show 0 ≤ 20*Real.exp 1*Real.exp (-(Real.log T/Real.log z)) by positivity)
  have hB := mul_le_mul_of_nonneg_right he2
    (show 0 ≤ 51*Real.exp 1*Real.exp (-(Real.log T/Real.log z)) by positivity)
  nlinarith

theorem upper_bound_of_lower (C : ℝ)
    (hlower : ∀ T z : ℝ, 2 ≤ z → z^2 ≤ T →
      normalizedLower T z ≤ C*Real.exp (-(Real.log T/Real.log z))) (T z : ℝ) :
    upperLoss T z / primeEuler z ≤ rejectedMass T z+C*acceptedExponentialMass T z := by
  rw [upperLoss_first_prime, Finset.sum_div]
  unfold rejectedMass acceptedExponentialMass acceptedPrimes
  rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  split_ifs with hg
  · have hpp := ((SieveSmallWeights.mem_pool z p).mp hp).1
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hp0 : (0:ℝ) < p := by linarith
    have hchild : (p:ℝ)^2 ≤ T/(p:ℝ) := by
      apply (le_div_iff₀ hp0).mpr
      simpa only [pow_succ] using hg.le
    have hb := mul_le_mul_of_nonneg_left (hlower (T/(p:ℝ)) (p:ℝ) hp2 hchild)
      (normalized_weight_nonneg p z)
    have heq : (PrimeEulerMass.weight p/primeEuler z)*normalizedLower (T/(p:ℝ)) (p:ℝ) =
        (p:ℝ)⁻¹*lowerLoss (T/(p:ℝ)) (p:ℝ)/primeEuler z := by
      unfold PrimeEulerMass.weight normalizedLower
      have hn := (SieveEulerRatio.euler_pos (p:ℝ)).ne'
      field_simp
    rw [heq] at hb
    convert hb using 1
    ring
  · simp only [PrimeEulerMass.weight, mul_zero, add_zero]
    exact le_rfl

theorem finite_cutoff_upper (T z z₀ : ℝ) (hz : 2 ≤ z) (hzz : z ≤ z₀) (hT : 1 ≤ T) :
    upperLoss T z/primeEuler z ≤
      SieveFiniteBase.exponentialConstant z₀*Real.exp (-(Real.log T/Real.log z)) := by
  by_cases hlevel : T < SieveFiniteBase.saturationLevel z₀
  · exact (SieveFiniteBase.normalized_losses_le T z z₀ hzz).2.trans
      (SieveFiniteBase.bounded_ratio_exponential z₀ (Real.log T/Real.log z)
        (SieveFiniteBase.ratio_le_logRange T z z₀ hT hz hlevel.le))
  · have hp : (((SieveSmallWeights.primes z₀).prod^3 : ℕ):ℝ) < T := by
      have hmax : ((((SieveSmallWeights.primes z₀).prod^3 : ℕ):ℝ)+1) ≤
          SieveFiniteBase.saturationLevel z₀ := le_max_right _ _
      linarith [le_of_not_gt hlevel]
    rw [(SieveFiniteSaturation.uniform_finite_cutoff T z z₀ hzz hp).2, zero_div]
    exact (mul_pos (SieveFiniteBase.exponentialConstant_pos z₀) (Real.exp_pos _)).le

def upperDecayConstant : ℝ := max (SieveFiniteBase.exponentialConstant SieveStoppingDecay.baseCutoff)
  ((72*Real.exp 1)*SieveStoppingDecay.decayConstant+11*Real.exp 3)

theorem upperDecayConstant_pos : 0 < upperDecayConstant :=
  lt_of_lt_of_le (SieveFiniteBase.exponentialConstant_pos _) (le_max_left _ _)

/-- The unconditional lower theorem is supplied to this exact upper recurrence. -/
theorem upper_decay_from_lower
    (hlower : ∀ T z : ℝ, 2 ≤ z → z^2 ≤ T → normalizedLower T z ≤
      SieveStoppingDecay.decayConstant*Real.exp (-(Real.log T/Real.log z)))
    (T z : ℝ) (hz : 2 ≤ z) (hT : z ≤ T) :
    upperLoss T z/primeEuler z ≤ upperDecayConstant*Real.exp (-(Real.log T/Real.log z)) := by
  by_cases hsmall : z ≤ SieveStoppingDecay.baseCutoff
  · exact (finite_cutoff_upper T z _ hz hsmall (by linarith)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · obtain ⟨hz64, _, heps⟩ :=
      SieveStoppingDecay.large_cutoff_conditions z hz (lt_of_not_ge hsmall)
    have hb := upper_bound_of_lower SieveStoppingDecay.decayConstant hlower T z
    have hr := rejectedMass_exponential T z hz64 hT heps
    have ha := mul_le_mul_of_nonneg_left (acceptedMass_bound T z hz hT heps)
      SieveStoppingDecay.decayConstant_pos.le
    calc
      _ ≤ (11*Real.exp 3)*Real.exp (-(Real.log T/Real.log z)) +
          SieveStoppingDecay.decayConstant*((72*Real.exp 1)*Real.exp (-(Real.log T/Real.log z))) :=
        hb.trans (add_le_add hr ha)
      _ = ((72*Real.exp 1)*SieveStoppingDecay.decayConstant+11*Real.exp 3)*
          Real.exp (-(Real.log T/Real.log z)) := by ring
      _ ≤ upperDecayConstant*Real.exp (-(Real.log T/Real.log z)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

theorem normalizedUpper_bound (T z : ℝ) (hz : 2 ≤ z) (hT : z ≤ T) :
    upperLoss T z/primeEuler z ≤ upperDecayConstant*Real.exp (-(Real.log T/Real.log z)) :=
  upper_decay_from_lower SieveStoppingDecay.normalizedLower_bound T z hz hT

theorem exists_upper_decay : ∃ C : ℝ, 0 < C ∧ ∀ T z : ℝ, 2 ≤ z → z ≤ T →
    upperLoss T z/primeEuler z ≤ C*Real.exp (-(Real.log T/Real.log z)) :=
  ⟨upperDecayConstant, upperDecayConstant_pos, fun T z hz hT => normalizedUpper_bound T z hz hT⟩

run_cmd do
  for decl in [``rejectedMass, ``rejectedMass_eq_zero, ``rejectedMass_le_interval,
      ``rejectedMass_bound, ``rejectedMass_exponential, ``acceptedMass_bound,
      ``upper_bound_of_lower, ``finite_cutoff_upper, ``upperDecayConstant,
      ``upperDecayConstant_pos, ``upper_decay_from_lower, ``normalizedUpper_bound,
      ``exists_upper_decay] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "UNCONDITIONAL ACTUAL NORMALIZED UPPER EXPONENTIAL DECAY PASSED"

end SieveStoppingUpperDecay
end
