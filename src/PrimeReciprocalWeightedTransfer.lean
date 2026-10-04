import PrimeReciprocalWeightedAbel

/-! A concrete reciprocal-log weight over actual finite prime intervals.
This supplies the changing-cutoff main-term input, without a sieve remainder
estimate or an assumed prime-density comparison. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real MeasureTheory Set
open scoped BigOperators
namespace PrimeReciprocalWeightedTransfer
open PrimeReciprocalWeightedAbel

def test (K t : ℝ) : ℝ := (K-log t)⁻¹
def testDerivative (K t : ℝ) : ℝ := t⁻¹/(K-log t)^2
def primitive (K t : ℝ) : ℝ := (log (log t)-log (K-log t))/K

theorem test_deriv (K t : ℝ) (ht : 1 < t) (hK : log t < K) :
    HasDerivAt (test K) (testDerivative K t) t := by
  have hn : K-log t ≠ 0 := (sub_pos.mpr hK).ne'
  convert! ((hasDerivAt_const t K).sub
    (hasDerivAt_log (by linarith : t ≠ 0))).inv hn using 1
  simp only [testDerivative, Pi.sub_apply, div_eq_mul_inv]
  ring

theorem test_continuous (K a b : ℝ) (ha : 1 < a) (hb : log b < K) :
    ContinuousOn (test K) (Icc a b) := by
  have hn : ∀ t ∈ Icc a b, t ≠ 0 := fun t ht => by linarith [ht.1]
  have hden : ∀ t ∈ Icc a b, K-log t ≠ 0 := by
    intro t ht
    have hlt := log_le_log (by linarith [ht.1] : 0 < t) ht.2
    exact (sub_pos.mpr (hlt.trans_lt hb)).ne'
  exact (continuousOn_const.sub (continuousOn_id.log hn)).inv₀ hden

theorem derivative_continuous (K a b : ℝ) (ha : 1 < a) (hb : log b < K) :
    ContinuousOn (testDerivative K) (Icc a b) := by
  have hn : ∀ t ∈ Icc a b, t ≠ 0 := fun t ht => by linarith [ht.1]
  have hden : ∀ t ∈ Icc a b, (K-log t)^2 ≠ 0 := by
    intro t ht
    have hlt := log_le_log (by linarith [ht.1] : 0 < t) ht.2
    exact pow_ne_zero 2 (sub_pos.mpr (hlt.trans_lt hb)).ne'
  exact (continuousOn_id.inv₀ hn).div
    ((continuousOn_const.sub (continuousOn_id.log hn)).pow 2) hden

theorem primitive_deriv (K t : ℝ) (ht : 1 < t) (hK : log t < K) :
    HasDerivAt (primitive K) (test K t*density t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog : log t ≠ 0 := (log_pos ht).ne'
  have hden : K-log t ≠ 0 := (sub_pos.mpr hK).ne'
  have hK0 : K ≠ 0 := ne_of_gt ((log_pos ht).trans hK)
  have hd := hasDerivAt_log ht0
  convert! ((hd.log hlog).sub
    (((hasDerivAt_const t K).sub hd).log hden)).div_const K using 1
  simp only [test, density, Pi.sub_apply]
  field_simp [ht0, hlog, hden, hK0]
  ring

theorem weighted_integral (K a b : ℝ) (ha : 1 < a) (hab : a ≤ b)
    (hb : log b < K) :
    (∫ t in a..b, test K t*density t) =
      (1/K)*log ((log b*(K-log a))/(log a*(K-log b))) := by
  have hb1 : 1 < b := ha.trans_le hab
  have hla := log_pos ha
  have hlb := log_pos hb1
  have haK : log a < K := (log_le_log (by linarith) hab).trans_lt hb
  have hi : IntervalIntegrable (fun t => test K t*density t) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact ((test_continuous K a b ha hb).mul
      (density_continuous a b ha)).integrableOn_Icc
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => by
      have htt : t ∈ Icc a b := (uIcc_of_le hab) ▸ ht
      exact primitive_deriv K t (ha.trans_le htt.1)
        ((log_le_log (by linarith [htt.1]) htt.2).trans_lt hb)) hi
  rw [hh]
  rw [log_div (mul_pos hlb (sub_pos.mpr haK)).ne'
      (mul_pos hla (sub_pos.mpr hb)).ne',
    log_mul hlb.ne' (sub_pos.mpr haK).ne',
    log_mul hla.ne' (sub_pos.mpr hb).ne']
  unfold primitive
  ring

theorem prime_reciprocal_log_bound (K a b : ℝ) (S : Finset ℕ)
    (ha : 1 < a) (hab : a ≤ b) (hb : log b < K)
    (hS : ∀ p ∈ S, p.Prime ∧ a ≤ (p:ℝ) ∧ (p:ℝ) ≤ b) :
    (∑ p ∈ S, (p:ℝ)⁻¹/(K-log (p:ℝ))) ≤
      (1/K)*log ((log b*(K-log a))/(log a*(K-log b)))+
        10/((K-log b)*log a) := by
  have haK : log a < K := (log_le_log (by linarith) hab).trans_lt hb
  have hh := weighted_bound S a b (test K) (testDerivative K) ha hab hS
    (inv_nonneg.mpr (sub_pos.mpr haK).le)
    (test_continuous K a b ha hb) (derivative_continuous K a b ha hb)
    (fun t ht => div_nonneg (inv_nonneg.mpr (by linarith [ht.1])) (sq_nonneg _))
    (fun t ht => test_deriv K t (ha.trans ht.1)
      ((log_le_log (by linarith [ht.1]) ht.2.le).trans_lt hb))
  rw [weighted_integral K a b ha hab hb] at hh
  convert hh using 1
  · apply Finset.sum_congr rfl
    intro p hp
    simp only [test, div_eq_mul_inv]
    ring
  · simp only [test, div_eq_mul_inv, mul_inv_rev]
    ring

/-- Explicit finite prime transfer in logarithmic exponent coordinates. -/
theorem prime_weighted_bound (X a b k : ℝ) (S : Finset ℕ)
    (hX : 1 < X) (ha : 0 < a) (hab : a ≤ b) (hbk : b < k)
    (hS : ∀ p ∈ S, p.Prime ∧ X^a ≤ (p:ℝ) ∧ (p:ℝ) ≤ X^b) :
    (∑ p ∈ S, (p:ℝ)⁻¹/(k-log (p:ℝ)/log X)) ≤
      (1/k)*log ((b*(k-a))/(a*(k-b)))+10/(a*(k-b)*log X) := by
  have hX0 : 0 < X := by linarith
  have hL : 0 < log X := log_pos hX
  have hk : 0 < k := by linarith
  have hka : 0 < k-a := by linarith
  have hkb : 0 < k-b := sub_pos.mpr hbk
  have hden0 : k*log X-b*log X ≠ 0 :=
    (sub_pos.mpr (mul_lt_mul_of_pos_right hbk hL)).ne'
  have hXa : 1 < X^a := one_lt_rpow hX ha
  have hXaXb : X^a ≤ X^b := rpow_le_rpow_of_exponent_le hX.le hab
  have hK : log (X^b) < k*log X := by
    rw [log_rpow hX0]
    exact mul_lt_mul_of_pos_right hbk hL
  have hh := mul_le_mul_of_nonneg_left
    (prime_reciprocal_log_bound (k*log X) (X^a) (X^b) S hXa hXaXb hK hS) hL.le
  rw [Finset.mul_sum] at hh
  have hsum : (∑ p ∈ S, log X*((p:ℝ)⁻¹/(k*log X-log (p:ℝ)))) =
      ∑ p ∈ S, (p:ℝ)⁻¹/(k-log (p:ℝ)/log X) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hp0 : 0 < (p:ℝ) := (by linarith : 0 < X^a).trans_le (hS p hp).2.1
    have hpl : log (p:ℝ) < k*log X :=
      (log_le_log hp0 (hS p hp).2.2).trans_lt hK
    have hden : k*log X-log (p:ℝ) ≠ 0 := (sub_pos.mpr hpl).ne'
    have hid : k-log (p:ℝ)/log X = (k*log X-log (p:ℝ))/log X := by
      field_simp [hL.ne']
    rw [hid]
    field_simp [hden, hL.ne', hp0.ne']
  rw [hsum] at hh
  simp only [log_rpow hX0] at hh
  have harg : (b*log X*(k*log X-a*log X))/(a*log X*(k*log X-b*log X)) =
      (b*(k-a))/(a*(k-b)) := by
    field_simp [ha.ne', hL.ne', hkb.ne', hden0]
  rw [harg] at hh
  convert hh using 1
  field_simp [hk.ne', ha.ne', hL.ne', hden0, hkb.ne']

run_cmd do
  for decl in [``test_deriv, ``test_continuous, ``derivative_continuous,
      ``primitive_deriv, ``weighted_integral, ``prime_reciprocal_log_bound,
      ``prime_weighted_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL RECIPROCAL-LOG PRIME TRANSFER CHECKED; BOTH ENDPOINTS INCLUDED"
end PrimeReciprocalWeightedTransfer
end
