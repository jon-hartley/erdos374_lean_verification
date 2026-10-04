import SieveStoppingTwoStep
import PrimeEulerMass
import PrimeEulerDimensionOne

/-! The actual rejected-gate forcing has compact logarithmic support and an
absolute bound once the dimension-one error is small. All sums here range
over the actual finite prime pools. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SieveStoppingForcing
open SieveStoppingExpansion SieveStoppingTwoStep PrimeEulerLogBounds

def root (x : ℝ) (n : ℕ) : ℝ := Real.exp (Real.log x / (n:ℝ))
def epsilon (z : ℝ) : ℝ := PrimeEulerDimensionOne.errorConstant / Real.log z

theorem root_lower (b x : ℝ) (n : ℕ) (hn : 0 < n) (hb : 0 < b)
    (hx : b^n ≤ x) : b ≤ root x n := by
  have hlog := Real.log_le_log (pow_pos hb n) hx
  rw [Real.log_pow] at hlog
  unfold root
  rw [← Real.exp_log hb]
  apply Real.exp_le_exp.mpr
  apply (le_div_iff₀ (by exact_mod_cast hn : (0:ℝ) < n)).mpr
  nlinarith

theorem root_le_self (x : ℝ) (n : ℕ) (hx : 1 ≤ x) (hn : 1 ≤ n) : root x n ≤ x := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hl := Real.log_nonneg hx
  unfold root
  calc
    _ ≤ Real.exp (Real.log x) := by
      apply Real.exp_le_exp.mpr
      apply (div_le_iff₀ hn0).mpr
      nlinarith
    _ = x := Real.exp_log (by linarith)

theorem rejected_level_lt_fourth (T p q : ℝ) (hp : 0 < p) (hq : 0 ≤ q)
    (hqp : q < p) (hfail : ¬q^3 < T/p) : T < p^4 := by
  have hf := (div_le_iff₀ hp).mp (le_of_not_gt hfail)
  have hm := mul_lt_mul_of_pos_right (pow_lt_pow_left₀ hqp hq (by decide : 3 ≠ 0)) hp
  nlinarith

theorem forcing_eq_zero (T z : ℝ) (hT : z^4 ≤ T) : forcing T z = 0 := by
  unfold forcing
  apply Finset.sum_eq_zero
  intro p hp
  apply Finset.sum_eq_zero
  intro q hq
  obtain ⟨hpp, hpz⟩ := (SieveSmallWeights.mem_pool z p).mp hp
  obtain ⟨_, hqp⟩ := (SieveSmallWeights.mem_pool (p:ℝ) q).mp hq
  have hp0 : (0:ℝ) < p := by exact_mod_cast hpp.pos
  have hg : (q:ℝ)^3 < T/(p:ℝ) := by
    by_contra hf
    have hlt := rejected_level_lt_fourth T (p:ℝ) (q:ℝ) hp0
      (Nat.cast_nonneg q) hqp hf
    have hpow := pow_lt_pow_left₀ hpz hp0.le (by decide : 4 ≠ 0)
    linarith
  simp only [hg, ite_true]

theorem rejected_outer_support (T z p q : ℝ) (hp : 0 < p) (hq : 0 ≤ q)
    (hpz : p < z) (hqp : q < p) (hT : z^2 ≤ T) (hfail : ¬q^3 < T/p) :
    root z 2 < p := by
  have hpow := hT.trans_lt (rejected_level_lt_fourth T p q hp hq hqp hfail)
  have hlog := Real.log_lt_log (pow_pos (hp.trans hpz) 2) hpow
  simp only [Real.log_pow, Nat.cast_ofNat] at hlog
  unfold root
  rw [← Real.exp_log hp]
  apply Real.exp_lt_exp.mpr
  norm_num
  linarith

theorem rejected_inner_support (T p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hT : p^2 < T) (hfail : ¬q^3 < T/p) : root p 3 < q := by
  have hf := (div_le_iff₀ hp).mp (le_of_not_gt hfail)
  have hqp : p < q^3 := by
    by_contra hn
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hp.le
    nlinarith
  have hlog := Real.log_lt_log hp hqp
  simp only [Real.log_pow, Nat.cast_ofNat] at hlog
  unfold root
  rw [← Real.exp_log hq]
  apply Real.exp_lt_exp.mpr
  norm_num
  linarith

theorem interval_eq_filter (a b : ℝ) :
    intervalPrimes a b = (SieveSmallWeights.pool b).filter (fun p : ℕ => a ≤ (p:ℝ)) := by
  ext p
  simp only [mem_intervalPrimes, Finset.mem_filter, SieveSmallWeights.mem_pool]
  tauto

def innerRejected (T : ℝ) (p : ℕ) : ℝ :=
  ∑ q ∈ SieveSmallWeights.pool (p:ℝ),
    if (q:ℝ)^3 < T/(p:ℝ) then 0
    else PrimeEulerMass.weight q / primeEuler (p:ℝ)

theorem normalized_weight_nonneg (p : ℕ) (z : ℝ) :
    0 ≤ PrimeEulerMass.weight p / primeEuler z :=
  div_nonneg (PrimeEulerMass.weight_nonneg p) (SieveEulerRatio.euler_pos z).le

theorem forcing_factored (T z : ℝ) : forcing T z =
    ∑ p ∈ SieveSmallWeights.pool z,
      (PrimeEulerMass.weight p / primeEuler z) * innerRejected T p := by
  unfold forcing innerRejected
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  split_ifs
  · simp
  · unfold PrimeEulerMass.weight
    have cancel (a b c d : ℝ) (hb : b ≠ 0) (hc : c ≠ 0) :
        a*b/c*(d/b) = a*d/c := by field_simp
    rw [cancel _ _ _ _ (SieveEulerRatio.euler_pos (p:ℝ)).ne'
      (SieveEulerRatio.euler_pos z).ne']
    ring

theorem innerRejected_le_interval (T : ℝ) (p : ℕ) (hp : (0:ℝ) < p)
    (hT : (p:ℝ)^2 < T) :
    innerRejected T p ≤ ∑ q ∈ intervalPrimes (root (p:ℝ) 3) (p:ℝ),
      PrimeEulerMass.weight q / primeEuler (p:ℝ) := by
  rw [interval_eq_filter, Finset.sum_filter]
  unfold innerRejected
  apply Finset.sum_le_sum
  intro q hq
  obtain ⟨hqp, _⟩ := (SieveSmallWeights.mem_pool (p:ℝ) q).mp hq
  have hq0 : (0:ℝ) < q := by exact_mod_cast hqp.pos
  by_cases hf : (q:ℝ)^3 < T/(p:ℝ)
  · simp only [hf, ite_true]
    split_ifs
    · exact normalized_weight_nonneg q _
    · exact le_rfl
  · have hs := (rejected_inner_support T (p:ℝ) (q:ℝ) hp hq0 hT hf).le
    simp only [hf, hs, ite_false, ite_true, le_refl]

theorem innerRejected_bound (T : ℝ) (p : ℕ) (hp8 : (8:ℝ) ≤ p)
    (hT : (p:ℝ)^2 < T) :
    innerRejected T p ≤ 2 + 9*PrimeEulerDimensionOne.errorConstant / Real.log (p:ℝ) := by
  have hp0 : (0:ℝ) < p := by linarith
  have hlog : Real.log (p:ℝ) ≠ 0 := (Real.log_pos (by linarith)).ne'
  have ha : 2 ≤ root (p:ℝ) 3 := root_lower 2 (p:ℝ) 3 (by norm_num) (by norm_num)
    (by norm_num at *; exact hp8)
  have hab := root_le_self (p:ℝ) 3 (by linarith) (by norm_num)
  apply (innerRejected_le_interval T p hp0 hT).trans
  apply (PrimeEulerMass.normalized_interval_bound _ _ ha hab).trans_eq
  simp only [root, Real.log_exp, Nat.cast_ofNat]
  field_simp
  ring

theorem innerRejected_zero_below (T z : ℝ) (p : ℕ)
    (hp : p ∈ SieveSmallWeights.pool z) (hT : z^2 ≤ T) (hpz : (p:ℝ) < root z 2) :
    innerRejected T p = 0 := by
  unfold innerRejected
  apply Finset.sum_eq_zero
  intro q hq
  obtain ⟨hpp, hpl⟩ := (SieveSmallWeights.mem_pool z p).mp hp
  obtain ⟨_, hql⟩ := (SieveSmallWeights.mem_pool (p:ℝ) q).mp hq
  have hp0 : (0:ℝ) < p := by exact_mod_cast hpp.pos
  have hg : (q:ℝ)^3 < T/(p:ℝ) := by
    by_contra hf
    have hs := rejected_outer_support T z (p:ℝ) (q:ℝ) hp0
      (Nat.cast_nonneg q) hpl hql hT hf
    linarith
  simp only [hg, ite_true]

theorem outer_interval_bound (z : ℝ) (hz : 64 ≤ z) :
    (∑ p ∈ intervalPrimes (root z 2) z, PrimeEulerMass.weight p / primeEuler z) ≤
      1+4*epsilon z := by
  have hlog : Real.log z ≠ 0 := (Real.log_pos (by linarith)).ne'
  have ha : 2 ≤ root z 2 := root_lower 2 z 2 (by norm_num) (by norm_num) (by nlinarith)
  have hab := root_le_self z 2 (by linarith) (by norm_num)
  apply (PrimeEulerMass.normalized_interval_bound _ _ ha hab).trans_eq
  simp only [root, Real.log_exp, Nat.cast_ofNat, epsilon]
  field_simp
  ring

theorem inner_uniform_bound (T z : ℝ) (p : ℕ) (hz : 64 ≤ z) (hT : z^2 ≤ T)
    (hp : p ∈ SieveSmallWeights.pool z) (hroot : root z 2 ≤ (p:ℝ)) :
    innerRejected T p ≤ 2+18*epsilon z := by
  obtain ⟨hpp, hpz⟩ := (SieveSmallWeights.mem_pool z p).mp hp
  have hp0 : (0:ℝ) < p := by exact_mod_cast hpp.pos
  have hp8 : (8:ℝ) ≤ p :=
    (root_lower 8 z 2 (by norm_num) (by norm_num) (by norm_num at *; exact hz)).trans hroot
  have hTp : (p:ℝ)^2 < T := (pow_lt_pow_left₀ hpz hp0.le (by decide : 2 ≠ 0)).trans_le hT
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlp := Real.log_le_log (Real.exp_pos (Real.log z / 2)) hroot
  simp only [Real.log_exp] at hlp
  have hdiv := div_le_div_of_nonneg_left PrimeEulerDimensionOne.errorConstant_pos.le
    (show 0 < Real.log z / 2 by positivity) hlp
  have he : PrimeEulerDimensionOne.errorConstant / Real.log (p:ℝ) ≤ 2*epsilon z := by
    convert hdiv using 1
    simp only [epsilon]
    ring
  have hb := innerRejected_bound T p hp8 hTp
  rw [mul_div_assoc] at hb
  linarith

theorem forcing_bound (T z : ℝ) (hz : 64 ≤ z) (hT : z^2 ≤ T) :
    forcing T z ≤ (2+18*epsilon z)*(1+4*epsilon z) := by
  have he0 : 0 ≤ epsilon z := div_nonneg PrimeEulerDimensionOne.errorConstant_pos.le
    (Real.log_pos (by linarith)).le
  have hc0 : 0 ≤ 2+18*epsilon z := by positivity
  rw [forcing_factored]
  calc
    _ ≤ ∑ p ∈ SieveSmallWeights.pool z,
        if root z 2 ≤ (p:ℝ) then
          (PrimeEulerMass.weight p / primeEuler z)*(2+18*epsilon z) else 0 := by
      apply Finset.sum_le_sum
      intro p hp
      split_ifs with hroot
      · exact mul_le_mul_of_nonneg_left (inner_uniform_bound T z p hz hT hp hroot)
          (normalized_weight_nonneg p z)
      · rw [innerRejected_zero_below T z p hp hT (lt_of_not_ge hroot), mul_zero]
    _ = (∑ p ∈ intervalPrimes (root z 2) z, PrimeEulerMass.weight p / primeEuler z) *
        (2+18*epsilon z) := by rw [interval_eq_filter, Finset.sum_mul, Finset.sum_filter]
    _ ≤ (1+4*epsilon z)*(2+18*epsilon z) :=
      mul_le_mul_of_nonneg_right (outer_interval_bound z hz) hc0
    _ = _ := mul_comm _ _

theorem forcing_le_hundred (T z : ℝ) (hz : 64 ≤ z) (hT : z^2 ≤ T)
    (he : epsilon z ≤ 1) : forcing T z ≤ 100 := by
  have he0 : 0 ≤ epsilon z := div_nonneg PrimeEulerDimensionOne.errorConstant_pos.le
    (Real.log_pos (by linarith)).le
  have hb := forcing_bound T z hz hT
  have hm := mul_le_mul (show 2+18*epsilon z ≤ 20 by linarith)
    (show 1+4*epsilon z ≤ 5 by linarith)
    (show 0 ≤ 1+4*epsilon z by positivity) (by norm_num : (0:ℝ) ≤ 20)
  nlinarith

theorem forcing_exponential (T z : ℝ) (hz : 64 ≤ z) (hT : z^2 ≤ T)
    (he : epsilon z ≤ 1) :
    forcing T z ≤ (100*Real.exp 4)*Real.exp (-(Real.log T / Real.log z)) := by
  by_cases hf : z^4 ≤ T
  · rw [forcing_eq_zero T z hf]
    positivity
  · have hz0 : 0 < z := by linarith
    have hT0 : 0 < T := (pow_pos hz0 2).trans_le hT
    have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
    have hlog := Real.log_lt_log hT0 (lt_of_not_ge hf)
    simp only [Real.log_pow, Nat.cast_ofNat] at hlog
    have hr : Real.log T / Real.log z < 4 := (div_lt_iff₀ hlogz).mpr (by linarith)
    apply (forcing_le_hundred T z hz hT he).trans
    rw [mul_assoc, ← Real.exp_add]
    have hpos : 1 ≤ Real.exp (4 + -(Real.log T / Real.log z)) := by
      calc
        (1:ℝ) = Real.exp 0 := by simp
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    nlinarith

run_cmd do
  for decl in [``root, ``epsilon, ``root_lower, ``root_le_self,
      ``rejected_level_lt_fourth, ``forcing_eq_zero, ``rejected_outer_support,
      ``rejected_inner_support, ``interval_eq_filter, ``innerRejected,
      ``normalized_weight_nonneg, ``forcing_factored, ``innerRejected_le_interval,
      ``innerRejected_bound, ``innerRejected_zero_below, ``outer_interval_bound,
      ``inner_uniform_bound, ``forcing_bound, ``forcing_le_hundred, ``forcing_exponential] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL FORCING SUPPORT AND EXPONENTIAL BOUND PASSED"

end SieveStoppingForcing
end
