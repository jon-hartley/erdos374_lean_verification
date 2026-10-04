import SieveUpperProfileCumulative
import SieveProfileExponentialTail

/-! Actual one-prime weighted bounds for the joined tail and bootstrap
exponential. These are finite arithmetic sums, with a uniform cutoff. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real
open scoped BigOperators
namespace SieveUpperProfileTail
open SieveUpperProfileCumulative SieveStoppingExpansion
open PrimeEulerExponentialCalculus

theorem child_ratio_identity (T : ℝ) (p : ℕ) (hT : 0 < T)
    (hp : 1 < (p:ℝ)) :
    log (T/(p:ℝ))/log (p:ℝ) = 10*((log T/10)/log (p:ℝ))-1 := by
  rw [log_div hT.ne' (show (p:ℝ) ≠ 0 by linarith)]
  field_simp [(log_pos hp).ne']

theorem tail_le_sum (T z : ℝ) (hT : 0 < T) :
    onePrime (fun T z => SieveProfileExponentialTail.tail (log T/log z)) T z ≤
      (91*exp (-189/10:ℝ))*
        ∑ p ∈ SieveSmallWeights.pool z,
          test (log T/10) p*(PrimeEulerMass.weight p/primeEuler z) := by
  unfold onePrime
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hp1 : 1 < (p:ℝ) := by
    exact_mod_cast ((SieveSmallWeights.mem_pool z p).mp hp).1.one_lt
  have hid := child_ratio_identity T p hT hp1
  unfold SieveProfileExponentialTail.tail
  dsimp only
  split_ifs with ht
  · have hb := SieveProfileTailScalar.tail_exp_bound
      (log (T/(p:ℝ))/log (p:ℝ)) ((log T/10)/log (p:ℝ)) ht hid.ge
    have hh := mul_le_mul_of_nonneg_left hb
      (mul_nonneg (weight_nonneg p z) (by norm_num : (0:ℝ) ≤ 91))
    convert hh using 1
    · ring
    · unfold test
      ring
  · have h := mul_nonneg (show (0:ℝ) ≤ 91*exp (-189/10:ℝ) by positivity)
      (mul_nonneg (test_pos (log T/10) p).le (weight_nonneg p z))
    simpa only [mul_zero] using h

theorem tail_bound (T z : ℝ) (hz : 2 ≤ z) (hT : z^3 ≤ T)
    (he : PrimeEulerDimensionOne.errorConstant/log z ≤ 1/100000) :
    onePrime (fun T z => SieveProfileExponentialTail.tail (log T/log z)) T z ≤
      (1/10000:ℝ) := by
  have hr := parameter_ge_three T z hz hT
  have hT0 : 0 < T := lt_of_lt_of_le (pow_pos (by linarith : 0 < z) 3) hT
  have hA : (1/10:ℝ) ≤ (2*(log T/10))/log z := by
    rw [show (2*(log T/10))/log z = (log T/log z)/5 by ring]
    linarith
  have hs := PrimeEulerProfileTail.small_parameter_sum_bound (2*(log T/10)) z hz hA
  rw [show 2*(log T/10)/2 = log T/10 by ring] at hs
  have he0 : 0 ≤ PrimeEulerDimensionOne.errorConstant/log z :=
    div_nonneg PrimeEulerDimensionOne.errorConstant_pos.le (log_pos (by linarith)).le
  have he1 : exp (1:ℝ) ≤ (2/5:ℝ)*20 := by linarith [exp_one_lt_three]
  have hcoef : 0 ≤ 20+841*(PrimeEulerDimensionOne.errorConstant/log z) := by positivity
  have hsum := hs.trans (mul_le_mul_of_nonneg_right he1 hcoef)
  have hb := (tail_le_sum T z hT0).trans
    (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 91*exp (-189/10:ℝ)))
  apply hb.trans
  convert SieveProfileTailScalar.final_tail_budget _ he0 he using 1
  ring

theorem exponential_identity (T z : ℝ) (hT : 0 < T) :
    onePrime (fun T z => exp (-(log T/log z))) T z =
      ∑ p ∈ SieveSmallWeights.pool z,
        test (log T) p*(PrimeEulerMass.weight p/primeEuler z) := by
  unfold onePrime
  apply Finset.sum_congr rfl
  intro p hp
  have hp1 : 1 < (p:ℝ) := by
    exact_mod_cast ((SieveSmallWeights.mem_pool z p).mp hp).1.one_lt
  have hid := child_ratio_identity T p hT hp1
  dsimp only
  rw [hid]
  unfold test
  rw [mul_comm]
  congr 2
  ring

theorem reciprocal_bounds (r : ℝ) (hr : 1 ≤ r) :
    1/r ≤ 1 ∧ 1+2*(r+1)/r^2 ≤ 5 := by
  have hr0 : 0 < r := by linarith
  have h1 : 1/r ≤ 1 := (div_le_iff₀ hr0).mpr (by linarith)
  have h2 : (1/r)^2 ≤ (1:ℝ)^2 := pow_le_pow_left₀ (by positivity) h1 2
  have hid : 1+2*(r+1)/r^2 = 1+2*(1/r)+2*(1/r)^2 := by field_simp; ring
  rw [hid]
  exact ⟨h1, by nlinarith⟩

theorem exponential_bound (T z : ℝ) (hz : 2 ≤ z) (hT : z^3 ≤ T)
    (he : PrimeEulerDimensionOne.errorConstant/log z ≤ 1/100000) :
    onePrime (fun T z => exp (-(log T/log z))) T z ≤ 1 := by
  have hr := parameter_ge_three T z hz hT
  have hT1 : 1 < T := by linarith [level_ge T z hz hT]
  have hlT : 0 < log T := log_pos hT1
  have he0 : 0 ≤ PrimeEulerDimensionOne.errorConstant/log z :=
    div_nonneg PrimeEulerDimensionOne.errorConstant_pos.le (log_pos (by linarith)).le
  obtain ⟨h1, h2⟩ := reciprocal_bounds (log T/log z) (by linarith)
  have he2 : exp (1-log T/log z) ≤ (45/331:ℝ) := by
    apply (exp_le_exp.mpr (show 1-log T/log z ≤ -2 by linarith)).trans
    rw [exp_neg]
    exact (inv_le_comm₀ (exp_pos 2) (by norm_num)).mpr
      (by simpa using SieveStoppingPositiveBudget.exp_two_lower)
  have hcoef : 1/(log T/log z)+(PrimeEulerDimensionOne.errorConstant/log z)*
      (1+2*(log T/log z+1)/(log T/log z)^2) ≤ 2 := by
    have hh := mul_le_mul_of_nonneg_left h2 he0
    linarith
  have hcoef0 : 0 ≤ 1/(log T/log z)+(PrimeEulerDimensionOne.errorConstant/log z)*
      (1+2*(log T/log z+1)/(log T/log z)^2) := by positivity
  rw [exponential_identity T z (by linarith)]
  apply (PrimeEulerExponentialBound.prime_exponential_sum_le (log T) z hlT hz).trans
  exact (mul_le_mul he2 hcoef hcoef0 (by norm_num)).trans (by norm_num)

theorem eventually_both :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^3 ≤ T →
      onePrime (fun T z => SieveProfileExponentialTail.tail (log T/log z)) T z ≤
        (1/10000:ℝ) ∧
      onePrime (fun T z => exp (-(log T/log z))) T z ≤ 1 := by
  let B := 100000*PrimeEulerDimensionOne.errorConstant
  refine ⟨max 2 (exp B), le_max_left _ _, ?_⟩
  intro z T hz hT
  have hz2 : 2 ≤ z := (le_max_left _ _).trans hz
  have hlz : 0 < log z := log_pos (by linarith)
  have hlog : B ≤ log z := by
    simpa only [log_exp] using log_le_log (exp_pos B) ((le_max_right _ _).trans hz)
  have he : PrimeEulerDimensionOne.errorConstant/log z ≤ 1/100000 := by
    apply (div_le_iff₀ hlz).mpr
    dsimp only [B] at hlog
    linarith
  exact ⟨tail_bound T z hz2 hT he, exponential_bound T z hz2 hT he⟩

run_cmd do
  for decl in [``child_ratio_identity, ``tail_le_sum, ``tail_bound,
      ``exponential_identity, ``reciprocal_bounds, ``exponential_bound,
      ``eventually_both] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL ONE-PRIME TAIL AND EXPONENTIAL ALLOWANCES CHECKED"
end SieveUpperProfileTail
end
