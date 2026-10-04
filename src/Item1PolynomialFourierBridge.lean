import Item1LogPhasePolynomialReduction
import Item1PolynomialMomentIdentity

/-! Exact conversion from angular polynomial phases to unit-torus characters.
Coordinate j represents degree j.val+1. Angular coefficients are divided by
2*pi because Mathlib's characters use the positive exponential exp(2*pi*i*n*x).
No estimate of an exponential sum or a polynomial moment is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open UnitAddTorus

namespace Item1PolynomialFourierBridge
open Item1PhasePerturbation Item1LogPhasePolynomialReduction
open Item1PolynomialMomentIdentity

/-- Convert angular coefficients to coordinates on the unit additive torus. -/
def coefficientPoint {d : ℕ} (a : Fin d → ℝ) : UnitAddTorus (Fin d) :=
  fun j => ((a j / (2*Real.pi) : ℝ) : UnitAddCircle)

/-- The character has the same positive sign as unitPhase after dividing by 2*pi. -/
theorem fourier_scaled_coefficient (n : ℤ) (a : ℝ) :
    fourier n ((a/(2*Real.pi) : ℝ) : UnitAddCircle) =
      unitPhase (a*(n:ℝ)) := by
  rw [fourier_coe_apply]
  simp only [unitPhase, Complex.ofReal_one, div_one, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_ofNat, Complex.ofReal_intCast]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpi] <;> ring

/-- A sum of angular integer frequencies is exactly a multivariate character. -/
theorem unitPhase_sum_eq_mFourier (d : ℕ) (a : Fin d → ℝ) (n : Fin d → ℤ) :
    unitPhase (∑ j, a j*(n j:ℝ)) = mFourier n (coefficientPoint a) := by
  simp only [mFourier, ContinuousMap.coe_mk, coefficientPoint,
    fourier_scaled_coefficient, unitPhase, Complex.ofReal_sum,
    Finset.sum_mul, Complex.exp_sum]

/-- Integer powers retain their degree and sign when cast to real angular phases. -/
theorem unitPhase_power_sum_eq_mFourier {ι : Type*} (d : ℕ)
    (a : Fin d → ℝ) (w : ι → ℤ) (i : ι) :
    unitPhase (∑ j : Fin d, a j*(w i:ℝ)^(j.val+1)) =
      mFourier (powerFrequency d w i) (coefficientPoint a) := by
  simpa only [powerFrequency, Int.cast_pow] using
    unitPhase_sum_eq_mFourier d a (powerFrequency d w i)

/-- The character conversion holds for every finite sum, retaining repetitions. -/
theorem finite_power_phase_sum_eq_mFourier {ι : Type*} (s : Finset ι) (d : ℕ)
    (a : Fin d → ℝ) (w : ι → ℤ) :
    (∑ i ∈ s, unitPhase (∑ j : Fin d, a j*(w i:ℝ)^(j.val+1))) =
      ∑ i ∈ s, mFourier (powerFrequency d w i) (coefficientPoint a) := by
  exact Finset.sum_congr rfl (fun i _ => unitPhase_power_sum_eq_mFourier d a w i)

/-- The normalized logarithmic coefficient agrees with the degree-(k+1) sign.
This identity also holds at x=0 under the usual totalized division convention. -/
theorem normalized_phaseCoefficient (x t : ℝ) (k : ℕ) :
    phaseCoefficient x t k / (2*Real.pi) =
      (-1:ℝ)^(k+1)*t / (2*Real.pi*((k:ℝ)+1)*x^(k+1)) := by
  unfold phaseCoefficient
  rw [pow_succ (-1:ℝ)]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The actual polynomial produced by the logarithmic Taylor reduction is a
unit-torus character at its displayed normalized coefficient vector. -/
theorem polynomialPhase_eq_mFourier {ι : Type*} (d : ℕ) (x t : ℝ)
    (w : ι → ℤ) (i : ι) :
    polynomialPhase d x t (w i:ℝ) =
      mFourier (powerFrequency d w i)
        (coefficientPoint (fun j : Fin d => phaseCoefficient x t j.val)) := by
  rw [polynomialPhase_eq, ← Fin.sum_univ_eq_sum_range
    (fun k : ℕ => phaseCoefficient x t k * (w i:ℝ)^(k+1))]
  exact unitPhase_power_sum_eq_mFourier d
    (fun j : Fin d => phaseCoefficient x t j.val) w i

/-- Exact finite-sum specialization for the Taylor polynomial phases. -/
theorem finite_polynomialPhase_sum_eq_mFourier {ι : Type*} (s : Finset ι)
    (d : ℕ) (x t : ℝ) (w : ι → ℤ) :
    (∑ i ∈ s, polynomialPhase d x t (w i:ℝ)) =
      ∑ i ∈ s, mFourier (powerFrequency d w i)
        (coefficientPoint (fun j : Fin d => phaseCoefficient x t j.val)) := by
  exact Finset.sum_congr rfl (fun i _ => polynomialPhase_eq_mFourier d x t w i)

end Item1PolynomialFourierBridge

run_cmd do
  for target in [``Item1PolynomialFourierBridge.fourier_scaled_coefficient,
      ``Item1PolynomialFourierBridge.unitPhase_sum_eq_mFourier,
      ``Item1PolynomialFourierBridge.unitPhase_power_sum_eq_mFourier,
      ``Item1PolynomialFourierBridge.finite_power_phase_sum_eq_mFourier,
      ``Item1PolynomialFourierBridge.normalized_phaseCoefficient,
      ``Item1PolynomialFourierBridge.polynomialPhase_eq_mFourier,
      ``Item1PolynomialFourierBridge.finite_polynomialPhase_sum_eq_mFourier] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "POLYNOMIAL FOURIER BRIDGE: 7 standard-axiom theorem guards passed."
