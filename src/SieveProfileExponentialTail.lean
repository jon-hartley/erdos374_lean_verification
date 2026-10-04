import PrimeEulerProfileTail
import SieveStoppingArithmeticContraction

/-! Uniform smallness of the actual two-prime exponential tail at child
ratio at least 20. The proof reorders finite prime sums and uses actual
reciprocal and exponential-sum estimates, without a continuum tail input. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Real
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace SieveProfileExponentialTail
open SieveStoppingExpansion SieveStoppingTwoStep PrimeEulerProfileTail
open PrimeEulerExponentialCalculus

def tail (r : ℝ) : ℝ := if 20 ≤ r then 91*exp (-r) else 0

theorem tail_nonneg (r : ℝ) : 0 ≤ tail r := by
  unfold tail
  split_ifs <;> positivity

theorem pool_below (z : ℝ) (p : ℕ) (hp : p ∈ SieveSmallWeights.pool z) :
    SieveSmallWeights.pool (p:ℝ) = (SieveSmallWeights.pool z).filter (fun q => q < p) := by
  ext q
  simp only [SieveSmallWeights.mem_pool, Finset.mem_filter]
  constructor
  · rintro ⟨hqp, hqp_lt⟩
    exact ⟨⟨hqp, hqp_lt.trans ((SieveSmallWeights.mem_pool z p).mp hp).2⟩,
      by exact_mod_cast hqp_lt⟩
  · rintro ⟨⟨hqp, _⟩, hqp_lt⟩
    exact ⟨hqp, by exact_mod_cast hqp_lt⟩

theorem finite_reordering (z : ℝ) (g : ℕ → ℝ) :
    (∑ p ∈ SieveSmallWeights.pool z, ∑ q ∈ SieveSmallWeights.pool (p:ℝ), (p:ℝ)⁻¹*g q) =
      ∑ q ∈ SieveSmallWeights.pool z, g q*outerReciprocal z q := by
  calc
    _ = ∑ p ∈ SieveSmallWeights.pool z, ∑ q ∈ SieveSmallWeights.pool z,
        if q < p then (p:ℝ)⁻¹*g q else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [pool_below z p hp, Finset.sum_filter]
    _ = ∑ q ∈ SieveSmallWeights.pool z, ∑ p ∈ SieveSmallWeights.pool z,
        if q < p then (p:ℝ)⁻¹*g q else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [outerReciprocal, Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> ring

theorem child_ratio_lower (T z : ℝ) (p q : ℕ) (hz : 2 ≤ z) (hT : z^2 ≤ T)
    (hp : p ∈ SieveSmallWeights.pool z) (hq : q ∈ SieveSmallWeights.pool (p:ℝ)) :
    10*(((log T-log z)/10)/log (q:ℝ))-1 ≤
      log ((T/(p:ℝ))/(q:ℝ))/log (q:ℝ) := by
  have hz0 : 0 < z := by linarith
  have hT0 : 0 < T := (pow_pos hz0 2).trans_le hT
  have hp0 : (0:ℝ) < p := by exact_mod_cast ((SieveSmallWeights.mem_pool z p).mp hp).1.pos
  have hq1 : (1:ℝ) < q := by exact_mod_cast ((SieveSmallWeights.mem_pool (p:ℝ) q).mp hq).1.one_lt
  have hq0 : (0:ℝ) < q := by linarith
  have hlq : 0 < log (q:ℝ) := log_pos hq1
  have hlp := log_le_log hp0 ((SieveSmallWeights.mem_pool z p).mp hp).2.le
  rw [log_div (div_pos hT0 hp0).ne' hq0.ne', log_div hT0.ne' hp0.ne']
  apply (le_div_iff₀ hlq).mpr
  have hid : (10*(((log T-log z)/10)/log (q:ℝ))-1)*log (q:ℝ) =
      log T-log z-log (q:ℝ) := by field_simp
  rw [hid]
  linarith

theorem tail_parameter (T z : ℝ) (hz : 2 ≤ z) (hT : z^2 ≤ T) :
    (1/10:ℝ) ≤ ((log T-log z)/10)/log z := by
  have hlz : 0 < log z := log_pos (by linarith)
  have hh := log_le_log (pow_pos (by linarith : 0 < z) 2) hT
  rw [log_pow] at hh
  apply (le_div_iff₀ hlz).mpr
  norm_num at hh
  linarith

theorem operator_tail_le_sum (T z : ℝ) (hz : 2 ≤ z) (hT : z^2 ≤ T) :
    operator (fun T z => tail (log T/log z)) T z ≤
      (91*exp (-189/10:ℝ)) *
        ∑ q ∈ SieveSmallWeights.pool z,
          (test ((log T-log z)/10) q*(PrimeEulerMass.weight q/primeEuler z))*outerReciprocal z q := by
  rw [← finite_reordering]
  unfold operator
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  have hqmass : 0 ≤ PrimeEulerMass.weight q/primeEuler z :=
    div_nonneg (PrimeEulerMass.weight_nonneg q) (SieveEulerRatio.euler_pos z).le
  have hw : 0 ≤ (p:ℝ)⁻¹*(q:ℝ)⁻¹*primeEuler (q:ℝ)/primeEuler z := by
    exact div_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p))
      (inv_nonneg.mpr (Nat.cast_nonneg q))) (SieveEulerRatio.euler_pos _).le)
      (SieveEulerRatio.euler_pos z).le
  have htarget : 0 ≤ 91*exp (-189/10:ℝ)*
      ((p:ℝ)⁻¹*(test ((log T-log z)/10) q*(PrimeEulerMass.weight q/primeEuler z))) := by
    exact mul_nonneg (by positivity) (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p))
      (mul_nonneg (test_pos _ _).le hqmass))
  split_ifs with hg
  · unfold tail
    dsimp only
    split_ifs with ht
    · have hs := mul_le_mul_of_nonneg_left
        (SieveProfileTailScalar.tail_exp_bound (log ((T/(p:ℝ))/(q:ℝ))/log (q:ℝ))
          (((log T-log z)/10)/log (q:ℝ)) ht (child_ratio_lower T z p q hz hT hp hq))
        (by norm_num : (0:ℝ) ≤ 91)
      have hh := mul_le_mul_of_nonneg_left hs hw
      convert hh using 1; unfold test PrimeEulerMass.weight; ring
    · simpa only [mul_zero] using htarget
  · exact htarget

theorem operator_tail_bound (T z : ℝ) (hz : 2 ≤ z) (hT : z^2 ≤ T)
    (hlog : 400 ≤ log z)
    (he : PrimeEulerDimensionOne.errorConstant/log z ≤ 1/100000) :
    operator (fun T z => tail (log T/log z)) T z ≤ (1/10000:ℝ) := by
  let A := (log T-log z)/10
  have hA := tail_parameter T z hz hT
  have hsum : (∑ q ∈ SieveSmallWeights.pool z,
      (test A q*(PrimeEulerMass.weight q/primeEuler z))*outerReciprocal z q) ≤
      (2/5:ℝ)*(20*(20+841*(PrimeEulerDimensionOne.errorConstant/log z))) := by
    calc
      _ ≤ (2/5:ℝ)*(∑ q ∈ SieveSmallWeights.pool z, (log z/log q)*test A q*
          (PrimeEulerMass.weight q/primeEuler z)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro q hq
        have hh := mul_le_mul_of_nonneg_left (outerReciprocal_bound z q hq hlog)
          (mul_nonneg (test_pos A q).le (div_nonneg (PrimeEulerMass.weight_nonneg q)
            (SieveEulerRatio.euler_pos z).le))
        convert hh using 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (weighted_prime_sum_bound A z hz hA) (by norm_num)
  have ho := (operator_tail_le_sum T z hz hT).trans
    (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 91*exp (-189/10:ℝ)))
  have he0 : 0 ≤ PrimeEulerDimensionOne.errorConstant/log z :=
    div_nonneg PrimeEulerDimensionOne.errorConstant_pos.le (log_pos (by linarith)).le
  apply ho.trans
  convert SieveProfileTailScalar.final_tail_budget _ he0 he using 1; ring

run_cmd do
  for decl in [``tail, ``tail_nonneg, ``pool_below, ``finite_reordering,
    ``child_ratio_lower, ``tail_parameter, ``operator_tail_le_sum, ``operator_tail_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL TWO-PRIME EXPONENTIAL TAIL AT CHILD RATIO 20 AT MOST 1/10000"
end SieveProfileExponentialTail
end
