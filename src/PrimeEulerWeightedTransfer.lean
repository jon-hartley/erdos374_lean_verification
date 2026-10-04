import PrimeEulerMass
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Weighted upper-tail transfer for the actual prime Euler measure.
The abstract finite identity accepts an integral representation, so it can also
be used with piecewise smooth test functions. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace PrimeEulerWeightedTransfer
open PrimeEulerLogBounds SieveStoppingExpansion

def finiteTail (S : Finset ℕ) (w : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ p ∈ S, if x ≤ (p : ℝ) then w p else 0

theorem mul_finiteTail_eq_sum_indicator (S : Finset ℕ) (w : ℕ → ℝ)
    (f : ℝ → ℝ) (x : ℝ) :
    f x * finiteTail S w x =
      ∑ p ∈ S, (Iic (p : ℝ)).indicator (fun t => w p * f t) x := by
  classical
  unfold finiteTail
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hx : x ≤ (p : ℝ)
  · simp [hx, Set.indicator, mul_comm]
  · simp [hx, Set.indicator]

theorem indicator_intervalIntegrable (f : ℝ → ℝ) (w : ℕ → ℝ)
    (a b : ℝ) (hf : IntervalIntegrable f volume a b) (p : ℕ) :
    IntervalIntegrable ((Iic (p : ℝ)).indicator (fun t => w p * f t))
      volume a b :=
  ⟨(hf.1.const_mul _).indicator measurableSet_Iic,
    (hf.2.const_mul _).indicator measurableSet_Iic⟩

theorem mul_finiteTail_intervalIntegrable (S : Finset ℕ) (w : ℕ → ℝ)
    (f : ℝ → ℝ) (a b : ℝ) (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t => f t * finiteTail S w t) volume a b := by
  classical
  have heq : (fun t => f t * finiteTail S w t) =
      (fun t => ∑ p ∈ S, (Iic (p : ℝ)).indicator (fun x => w p * f x) t) :=
    funext (mul_finiteTail_eq_sum_indicator S w f)
  rw [heq]
  convert! IntervalIntegrable.sum S
    (fun p _ => indicator_intervalIntegrable f w a b hf p) using 1
  ext t
  simp only [Finset.sum_apply]

theorem integral_mul_finiteTail (S : Finset ℕ) (w : ℕ → ℝ)
    (f : ℝ → ℝ) (a b : ℝ) (hf : IntervalIntegrable f volume a b)
    (hS : ∀ p ∈ S, (p : ℝ) ∈ Icc a b) :
    (∫ t in a..b, f t * finiteTail S w t) =
      ∑ p ∈ S, w p * ∫ t in a..(p : ℝ), f t := by
  classical
  simp_rw [mul_finiteTail_eq_sum_indicator]
  rw [intervalIntegral.integral_finsetSum
    (fun p _ => indicator_intervalIntegrable f w a b hf p)]
  apply Finset.sum_congr rfl
  intro p hp
  change (∫ x in a..b, {x : ℝ | x ≤ (p : ℝ)}.indicator
    (fun t => w p * f t) x) = _
  rw [intervalIntegral.integral_indicator (hS p hp),
    intervalIntegral.integral_const_mul]

/-- Exact finite summation by parts. The representation hypothesis can be
established by FTC for C1 tests or separately for piecewise smooth tests. -/
theorem weighted_sum_eq_tail_integral (S : Finset ℕ) (w : ℕ → ℝ)
    (φ f : ℝ → ℝ) (a b : ℝ) (hf : IntervalIntegrable f volume a b)
    (hS : ∀ p ∈ S, (p : ℝ) ∈ Icc a b)
    (hφ : ∀ p ∈ S, φ (p : ℝ) = φ a + ∫ t in a..(p : ℝ), f t) :
    (∑ p ∈ S, φ (p : ℝ) * w p) =
      φ a * (∑ p ∈ S, w p) + ∫ t in a..b, f t * finiteTail S w t := by
  rw [integral_mul_finiteTail S w f a b hf hS, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [hφ p hp]
  ring

theorem prime_finiteTail (a b x : ℝ) (hax : a ≤ x) :
    finiteTail (intervalPrimes a b) (fun p => PrimeEulerMass.weight p / primeEuler b) x =
      ∑ p ∈ intervalPrimes x b, PrimeEulerMass.weight p / primeEuler b := by
  classical
  unfold finiteTail
  rw [← Finset.sum_filter]
  congr 1
  ext p
  rw [Finset.mem_filter, mem_intervalPrimes, mem_intervalPrimes]
  constructor
  · rintro ⟨⟨hp, hpb, _⟩, hxp⟩
    exact ⟨hp, hpb, hxp⟩
  · rintro ⟨hp, hpb, hxp⟩
    exact ⟨⟨hp, hpb, hax.trans hxp⟩, hxp⟩

def tailBound (x b : ℝ) : ℝ :=
  Real.log b / Real.log x - 1 +
    PrimeEulerDimensionOne.errorConstant * Real.log b / (Real.log x)^2

theorem tailBound_continuousOn (a b : ℝ) (ha : 2 ≤ a) :
    ContinuousOn (fun x => tailBound x b) (Icc a b) := by
  have hn : ∀ x ∈ Icc a b, x ≠ 0 := fun x hx => by linarith [hx.1]
  have hl : ∀ x ∈ Icc a b, Real.log x ≠ 0 := fun x hx =>
    (Real.log_pos (by linarith [hx.1])).ne'
  exact ((continuousOn_const.div (continuousOn_id.log hn) hl).sub
    continuousOn_const).add
      (continuousOn_const.div ((continuousOn_id.log hn).pow 2)
        (fun x hx => pow_ne_zero 2 (hl x hx)))

/-- Arithmetic transfer under an analytic integral representation. All prime
distribution input is discharged by the actual normalized interval theorem. -/
theorem prime_weighted_transfer_of_integral (φ f : ℝ → ℝ) (a b : ℝ)
    (ha : 2 ≤ a) (hab : a ≤ b) (hφa : 0 ≤ φ a)
    (hfi : IntervalIntegrable f volume a b) (hf0 : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hφ : ∀ p ∈ intervalPrimes a b,
      φ (p : ℝ) = φ a + ∫ t in a..(p : ℝ), f t) :
    (∑ p ∈ intervalPrimes a b, φ (p : ℝ) *
      (PrimeEulerMass.weight p / primeEuler b)) ≤
      φ a * tailBound a b + ∫ t in a..b, f t * tailBound t b := by
  have hgi : IntervalIntegrable (fun t => f t * tailBound t b) volume a b := by
    apply hfi.mul_continuousOn
    simpa only [uIcc_of_le hab] using (tailBound_continuousOn a b ha)
  rw [weighted_sum_eq_tail_integral _ _ φ f a b hfi
    (fun p hp => ⟨((mem_intervalPrimes a b p).mp hp).2.2,
      ((mem_intervalPrimes a b p).mp hp).2.1.le⟩) hφ]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left
      (PrimeEulerMass.normalized_interval_bound a b ha hab) hφa
  · apply intervalIntegral.integral_mono_on hab
      (mul_finiteTail_intervalIntegrable _ _ f a b hfi) hgi
    intro t ht
    rw [prime_finiteTail a b t ht.1]
    exact mul_le_mul_of_nonneg_left
      (PrimeEulerMass.normalized_interval_bound t b (ha.trans ht.1) ht.2) (hf0 t ht)

/-- The derivative is required only on the open interval; continuity is local
to the closed interval. No global smoothness assumption is imposed. -/
theorem prime_weighted_transfer (φ f : ℝ → ℝ) (a b : ℝ)
    (ha : 2 ≤ a) (hab : a ≤ b) (hφa : 0 ≤ φ a)
    (hφ : ContinuousOn φ (Icc a b))
    (hf : ContinuousOn f (Icc a b)) (hf0 : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt φ (f x) x) :
    (∑ p ∈ intervalPrimes a b, φ (p : ℝ) *
      (PrimeEulerMass.weight p / primeEuler b)) ≤
      φ a * tailBound a b + ∫ t in a..b, f t * tailBound t b := by
  have hfiab : IntervalIntegrable f volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hf.integrableOn_Icc
  apply prime_weighted_transfer_of_integral φ f a b ha hab hφa hfiab hf0
  intro p hp
  have hpa := ((mem_intervalPrimes a b p).mp hp).2.2
  have hpb := ((mem_intervalPrimes a b p).mp hp).2.1
  have hsub : Icc a (p : ℝ) ⊆ Icc a b := fun t ht => ⟨ht.1, ht.2.trans hpb.le⟩
  have hfi : IntervalIntegrable f volume a (p : ℝ) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hpa]
    exact (hf.mono hsub).integrableOn_Icc
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hpa
    (hφ.mono hsub) (fun t ht => hd t ⟨ht.1, ht.2.trans hpb⟩) hfi
  linarith

def tailDensity (x b : ℝ) : ℝ :=
  Real.log b / (x * (Real.log x)^2) +
    2 * PrimeEulerDimensionOne.errorConstant * Real.log b / (x * (Real.log x)^3)

theorem tailDensity_continuousOn (a b : ℝ) (ha : 2 ≤ a) :
    ContinuousOn (fun x => tailDensity x b) (Icc a b) := by
  have hn : ∀ x ∈ Icc a b, x ≠ 0 := fun x hx => by linarith [hx.1]
  have hl : ∀ x ∈ Icc a b, Real.log x ≠ 0 := fun x hx =>
    (Real.log_pos (by linarith [hx.1])).ne'
  exact (continuousOn_const.div
    (continuousOn_id.mul ((continuousOn_id.log hn).pow 2))
      (fun x hx => mul_ne_zero (hn x hx) (pow_ne_zero 2 (hl x hx)))).add
    (continuousOn_const.div
      (continuousOn_id.mul ((continuousOn_id.log hn).pow 3))
        (fun x hx => mul_ne_zero (hn x hx) (pow_ne_zero 3 (hl x hx))))

theorem tailBound_hasDerivAt (x b : ℝ) (hx : 1 < x) :
    HasDerivAt (fun t => tailBound t b) (-tailDensity x b) x := by
  have hx0 : x ≠ 0 := by linarith
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hd := Real.hasDerivAt_log hx0
  have h1 := ((hasDerivAt_const x (Real.log b)).div hd hl).sub_const 1
  have h2 := (hasDerivAt_const x
    (PrimeEulerDimensionOne.errorConstant * Real.log b)).div (hd.pow 2) (pow_ne_zero 2 hl)
  convert! h1.add h2 using 1
  dsimp [tailDensity]
  field_simp
  ring

theorem tailBound_self (b : ℝ) (hb : 1 < b) :
    tailBound b b = PrimeEulerDimensionOne.errorConstant / Real.log b := by
  have hl : Real.log b ≠ 0 := (Real.log_pos hb).ne'
  unfold tailBound
  rw [div_self hl]
  field_simp
  ring

/-- Exact conversion of the derivative-weight tail expression to the explicit
comparison density, including its positive upper-endpoint error. -/
theorem tail_integration_by_parts (φ f : ℝ → ℝ) (a b : ℝ)
    (ha : 2 ≤ a) (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b))
    (hf : IntervalIntegrable f volume a b)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt φ (f x) x) :
    φ a * tailBound a b + (∫ t in a..b, f t * tailBound t b) =
      φ b * (PrimeEulerDimensionOne.errorConstant / Real.log b) +
        ∫ t in a..b, φ t * tailDensity t b := by
  have hI1 : IntervalIntegrable (fun t => f t * tailBound t b) volume a b :=
    hf.mul_continuousOn (by simpa only [uIcc_of_le hab] using
      (tailBound_continuousOn a b ha))
  have hI2 : IntervalIntegrable (fun t => φ t * tailDensity t b) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact (hφ.mul (tailDensity_continuousOn a b ha)).integrableOn_Icc
  have hp : ∀ t ∈ Ioo a b, HasDerivAt (fun x => φ x * tailBound x b)
      (f t * tailBound t b - φ t * tailDensity t b) t := by
    intro t ht
    convert! (hd t ht).mul (tailBound_hasDerivAt t b (by linarith [ht.1])) using 1
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (hφ.mul (tailBound_continuousOn a b ha)) hp (hI1.sub hI2)
  simp only [Pi.mul_apply] at hi
  rw [intervalIntegral.integral_sub hI1 hI2,
    tailBound_self b (by linarith)] at hi
  linarith

/-- Actual-prime weighted transfer in density form. Its endpoint term is the
arithmetic comparison error at the upper cutoff, not a prime atom at b. -/
theorem prime_weighted_transfer_density (φ f : ℝ → ℝ) (a b : ℝ)
    (ha : 2 ≤ a) (hab : a ≤ b) (hφa : 0 ≤ φ a)
    (hφ : ContinuousOn φ (Icc a b))
    (hf : ContinuousOn f (Icc a b)) (hf0 : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt φ (f x) x) :
    (∑ p ∈ intervalPrimes a b, φ (p : ℝ) *
      (PrimeEulerMass.weight p / primeEuler b)) ≤
      φ b * (PrimeEulerDimensionOne.errorConstant / Real.log b) +
        ∫ t in a..b, φ t * tailDensity t b := by
  have hfi : IntervalIntegrable f volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hf.integrableOn_Icc
  calc
    _ ≤ φ a * tailBound a b + ∫ t in a..b, f t * tailBound t b :=
      prime_weighted_transfer φ f a b ha hab hφa hφ hf hf0 hd
    _ = _ := tail_integration_by_parts φ f a b ha hab hφ hfi hd

run_cmd do
  for decl in [``mul_finiteTail_eq_sum_indicator, ``indicator_intervalIntegrable,
    ``mul_finiteTail_intervalIntegrable, ``integral_mul_finiteTail,
    ``weighted_sum_eq_tail_integral, ``prime_finiteTail, ``tailBound_continuousOn,
    ``prime_weighted_transfer_of_integral, ``prime_weighted_transfer,
    ``tailDensity_continuousOn, ``tailBound_hasDerivAt, ``tailBound_self,
    ``tail_integration_by_parts, ``prime_weighted_transfer_density] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL PRIME WEIGHTED UPPER-TAIL TRANSFER PASSED"

end PrimeEulerWeightedTransfer
end
