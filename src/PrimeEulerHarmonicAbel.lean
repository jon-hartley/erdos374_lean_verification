import PrimeEulerWeightedTransfer
import MertensPrimeInterval

/-! A closed-prime-range logarithmic harmonic majorant. Finite Abel
summation and the actual reciprocal-prime bound retain both endpoints. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real MeasureTheory Set
open scoped BigOperators
namespace PrimeEulerHarmonicAbel
open PrimeEulerWeightedTransfer

def head (S : Finset ℕ) (w : ℕ → ℝ) (t : ℝ) : ℝ :=
  (∑ p ∈ S, w p)-finiteTail S w t

theorem head_eq_filter (S : Finset ℕ) (w : ℕ → ℝ) (t : ℝ) :
    head S w t = ∑ p ∈ S.filter (fun p : ℕ => (p:ℝ) < t), w p := by
  classical
  rw [head, finiteTail, ← Finset.sum_sub_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : t ≤ (p:ℝ)
  · simp [h, not_lt.mpr h]
  · simp [h, lt_of_not_ge h]

theorem inv_integrable (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => t⁻¹) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  exact (continuousOn_id.inv₀ (fun t ht => by
    change t ≠ 0
    linarith [ht.1])).integrableOn_Icc

theorem head_integrable (S : Finset ℕ) (w : ℕ → ℝ) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => t⁻¹*head S w t) volume a b := by
  have hf := inv_integrable a b ha hab
  have hh := (hf.mul_const (∑ p ∈ S, w p)).sub
    (mul_finiteTail_intervalIntegrable S w _ a b hf)
  simpa only [head, mul_sub] using hh

theorem weighted_log_identity (S : Finset ℕ) (w : ℕ → ℝ) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hS : ∀ p ∈ S, (p:ℝ) ∈ Icc a b) :
    (∑ p ∈ S, (1+log b-log (p:ℝ))*w p) =
      (∑ p ∈ S, w p)+∫ t in a..b, t⁻¹*head S w t := by
  have hb : 0 < b := ha.trans_le hab
  have hf := inv_integrable a b ha hab
  have hrep : ∀ p ∈ S, log (p:ℝ) = log a+∫ t in a..(p:ℝ), t⁻¹ := by
    intro p hp
    have hp0 : 0 < (p:ℝ) := ha.trans_le (hS p hp).1
    rw [integral_inv_of_pos ha hp0, log_div hp0.ne' ha.ne']
    ring
  have hsum := weighted_sum_eq_tail_integral S w log (fun t => t⁻¹) a b hf hS hrep
  have hi : (∫ t in a..b, t⁻¹*head S w t) =
      (log b-log a)*(∑ p ∈ S, w p)-∫ t in a..b, t⁻¹*finiteTail S w t := by
    simp only [head, mul_sub]
    rw [intervalIntegral.integral_sub (hf.mul_const _) (mul_finiteTail_intervalIntegrable S w _ a b hf),
      intervalIntegral.integral_mul_const, integral_inv_of_pos ha hb, log_div hb.ne' ha.ne']
  have hleft : (∑ p ∈ S, (1+log b-log (p:ℝ))*w p) =
      (1+log b)*(∑ p ∈ S, w p)-(∑ p ∈ S, log (p:ℝ)*w p) := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hleft, hi, hsum]
  ring

def primitive (L t : ℝ) : ℝ := log t*log (log t/L)-log t

theorem primitive_deriv (L t : ℝ) (hL : 0 < L) (ht : 1 < t) :
    HasDerivAt (primitive L) (t⁻¹*log (log t/L)) t := by
  have ht0 : 0 < t := by linarith
  have hlt : 0 < log t := log_pos ht
  have h1 := hasDerivAt_log ht0.ne'
  have h2 := (h1.div_const L).log (div_pos hlt hL).ne'
  convert (h1.mul h2).sub h1 using 1
  · rfl
  · field_simp
    ring

theorem log_kernel_continuous (L a b : ℝ) (hL : 0 < L) (ha : 1 < a) :
    ContinuousOn (fun t => t⁻¹*log (log t/L)) (Icc a b) := by
  have hn : ∀ t ∈ Icc a b, t ≠ 0 := fun t ht => by linarith [ht.1]
  have hl : ∀ t ∈ Icc a b, log t/L ≠ 0 :=
    fun t ht => (div_pos (log_pos (ha.trans_le ht.1)) hL).ne'
  exact (continuousOn_id.inv₀ hn).mul
    (((continuousOn_id.log hn).div_const L).log hl)

theorem log_kernel_integral (z : ℝ) (hz : 1 < z) :
    (∫ t in z..z^2, t⁻¹*log (log t/log z)) = (2*log 2-1)*log z := by
  have hz0 : 0 < z := by linarith
  have hzz : z ≤ z^2 := by nlinarith
  have hlz := log_pos hz
  have hi : IntervalIntegrable (fun t => t⁻¹*log (log t/log z)) volume z (z^2) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hzz]
    exact (log_kernel_continuous (log z) z (z^2) hlz hz).integrableOn_Icc
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => primitive_deriv (log z) t hlz
      (hz.trans_le ((uIcc_of_le hzz ▸ ht) : t ∈ Icc z (z^2)).1)) hi
  rw [hh]
  simp only [primitive, log_pow, Nat.cast_ofNat,
    mul_div_cancel_right₀ _ hlz.ne', div_self hlz.ne', log_one, mul_zero]
  ring

theorem prime_weighted_log_bound (z : ℝ) (S : Finset ℕ) (hz : 1 < z)
    (hS : ∀ p ∈ S, p.Prime ∧ z ≤ (p:ℝ) ∧ (p:ℝ) ≤ z^2) :
    (∑ p ∈ S, (1+2*log z-log (p:ℝ))*(p:ℝ)⁻¹) ≤
      (2*log 2-1)*log z+10+log 2+10/log z := by
  classical
  have hz0 : 0 < z := by linarith
  have hzz : z ≤ z^2 := by nlinarith
  have hlz : 0 < log z := log_pos hz
  have hf := inv_integrable z (z^2) hz0 hzz
  have hlog : IntervalIntegrable (fun t => t⁻¹*log (log t/log z)) volume z (z^2) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hzz]
    exact (log_kernel_continuous (log z) z (z^2) hlz hz).integrableOn_Icc
  have hmass := MertensPrimeInterval.prime_reciprocal_interval z (z^2) S hz hzz hS
  rw [log_pow, Nat.cast_ofNat, mul_div_cancel_right₀ _ hlz.ne'] at hmass
  have hhead : ∀ t ∈ Icc z (z^2), head S (fun p => (p:ℝ)⁻¹) t ≤
      log (log t/log z)+10/log z := by
    intro t ht
    rw [head_eq_filter]
    apply MertensPrimeInterval.prime_reciprocal_interval z t _ hz ht.1
    intro p hp
    obtain ⟨hpS, hpt⟩ := Finset.mem_filter.mp hp
    exact ⟨(hS p hpS).1, (hS p hpS).2.1, hpt.le⟩
  have hi := intervalIntegral.integral_mono_on hzz
    (head_integrable S (fun p => (p:ℝ)⁻¹) z (z^2) hz0 hzz)
    (hlog.add (hf.mul_const (10/log z))) (fun t ht => show
      t⁻¹*head S (fun p => (p:ℝ)⁻¹) t ≤
        t⁻¹*log (log t/log z)+t⁻¹*(10/log z) from by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (hhead t ht) (by
        exact inv_nonneg.mpr (hz0.le.trans ht.1)))
  rw [intervalIntegral.integral_add hlog (hf.mul_const _),
    intervalIntegral.integral_mul_const, log_kernel_integral z hz,
    integral_inv_of_pos hz0 (pow_pos hz0 2),
    log_div (pow_pos hz0 2).ne' hz0.ne', log_pow] at hi
  have hii : (∫ t in z..z^2, t⁻¹*head S (fun p => (p:ℝ)⁻¹) t) ≤
      (2*log 2-1)*log z+10 := by
    convert hi using 1
    norm_num
    field_simp
    ring
  have heq := weighted_log_identity S (fun p => (p:ℝ)⁻¹) z (z^2) hz0 hzz
    (fun p hp => ⟨(hS p hp).2.1, (hS p hp).2.2⟩)
  rw [log_pow, Nat.cast_ofNat] at heq
  rw [heq]
  linarith

run_cmd do
  for decl in [``head_eq_filter, ``inv_integrable, ``head_integrable,
      ``weighted_log_identity, ``primitive_deriv, ``log_kernel_continuous,
      ``log_kernel_integral, ``prime_weighted_log_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL CLOSED-RANGE WEIGHTED PRIME LOGARITHMIC BOUND CHECKED"
end PrimeEulerHarmonicAbel
end
