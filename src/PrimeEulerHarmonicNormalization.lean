import PrimeEulerHarmonicBounds
import PrimeEulerHarmonicAbel
import Mathlib.Analysis.Complex.ExponentialBounds

/-! An elementary absolute upper normalization for the actual strict
prime Euler product. No absolute Mertens constant or prime number theorem
is used: finite smooth harmonic mass and the actual prime interval bound suffice. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real Filter
open scoped BigOperators
namespace PrimeEulerHarmonicNormalization
open PrimeEulerHarmonicSmooth PrimeEulerHarmonicBounds SieveStoppingExpansion

theorem inverse_lower_explicit (z : ℝ) (hz : 2 ≤ z) :
    (3-2*log 2)*log z-10-log 2-10/log z ≤ (primeEuler z)⁻¹ := by
  have ha := PrimeEulerHarmonicAbel.prime_weighted_log_bound z
    (excludedPrimes z ⌊z^2⌋₊) (by linarith : 1 < z)
    (fun p hp => excluded_properties z (z^2) (sq_nonneg z) p hp)
  have hw : (∑ p ∈ excludedPrimes z ⌊z^2⌋₊,
      (p:ℝ)⁻¹*(1+2*log z-log (p:ℝ))) ≤
      (2*log 2-1)*log z+10+log 2+10/log z := by
    simpa only [mul_comm] using ha
  have hh := inverse_lower_log_square z
  nlinarith

theorem explicit_coefficient_lower (L : ℝ) (hL : 1000 ≤ L) :
    (8/5:ℝ)*L ≤ (3-2*log 2)*L-10-log 2-10/L := by
  have hlog : log 2 ≤ (25/36:ℝ) := by linarith [log_two_lt_d9]
  have hdiv : (10:ℝ)/L ≤ 1/100 :=
    (div_le_iff₀ (by linarith : 0 < L)).mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_right
    (show (29/18:ℝ) ≤ 3-2*log 2 by linarith) (by linarith : 0 ≤ L)
  nlinarith

theorem product_log_bound (z : ℝ) (hz : 2 ≤ z) (hlog : 1000 ≤ log z) :
    primeEuler z*log z ≤ (5/8:ℝ) := by
  have hh := (explicit_coefficient_lower (log z) hlog).trans (inverse_lower_explicit z hz)
  have hm := mul_le_mul_of_nonneg_right hh (SieveEulerRatio.euler_pos z).le
  rw [inv_mul_cancel₀ (SieveEulerRatio.euler_pos z).ne'] at hm
  nlinarith

theorem bound_above_exp (z : ℝ) (hz : exp 1000 ≤ z) :
    primeEuler z*log z ≤ (5/8:ℝ) := by
  have h2 : (2:ℝ) ≤ exp 1000 := by linarith [add_one_le_exp (1000:ℝ)]
  have hl : (1000:ℝ) ≤ log z := by
    simpa only [log_exp] using log_le_log (exp_pos (1000:ℝ)) hz
  exact product_log_bound z (h2.trans hz) hl

theorem eventually_product_log_bound :
    ∀ᶠ z : ℝ in atTop, primeEuler z*log z ≤ (5/8:ℝ) := by
  filter_upwards [eventually_ge_atTop (exp (1000:ℝ))] with z hz
  exact bound_above_exp z hz

run_cmd do
  for decl in [``inverse_lower_explicit, ``explicit_coefficient_lower,
      ``product_log_bound, ``bound_above_exp, ``eventually_product_log_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL STRICT PRIME EULER PRODUCT: V(Z)*LOG Z AT MOST 5/8 ABOVE EXP(1000)"

end PrimeEulerHarmonicNormalization
end
