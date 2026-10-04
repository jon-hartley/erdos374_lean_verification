import PrimeEulerWeightedTransfer

/-! Actual-prime transfer with an integrable right derivative. Continuous
piecewise smooth tests are allowed; no derivative continuity at a join is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators
open Set MeasureTheory
namespace PrimeEulerRightTransfer
open PrimeEulerWeightedTransfer PrimeEulerLogBounds SieveStoppingExpansion

theorem tail_integration_by_parts_right (φ f : ℝ → ℝ) (a b : ℝ)
    (ha : 2 ≤ a) (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b))
    (hf : IntervalIntegrable f volume a b)
    (hd : ∀ x ∈ Ioo a b, HasDerivWithinAt φ (f x) (Ioi x) x) :
    φ a * tailBound a b + (∫ t in a..b, f t * tailBound t b) =
      φ b * (PrimeEulerDimensionOne.errorConstant / Real.log b) +
        ∫ t in a..b, φ t * tailDensity t b := by
  have hI1 : IntervalIntegrable (fun t => f t * tailBound t b) volume a b :=
    hf.mul_continuousOn (by simpa only [uIcc_of_le hab] using tailBound_continuousOn a b ha)
  have hI2 : IntervalIntegrable (fun t => φ t * tailDensity t b) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact (hφ.mul (tailDensity_continuousOn a b ha)).integrableOn_Icc
  have hp : ∀ t ∈ Ioo a b, HasDerivWithinAt (fun x => φ x * tailBound x b)
      (f t * tailBound t b - φ t * tailDensity t b) (Ioi t) t := by
    intro t ht
    convert! (hd t ht).mul ((tailBound_hasDerivAt t b
      (by linarith [ht.1])).hasDerivWithinAt) using 1
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    (hφ.mul (tailBound_continuousOn a b ha)) hp (hI1.sub hI2)
  simp only [Pi.mul_apply] at hi
  rw [intervalIntegral.integral_sub hI1 hI2, tailBound_self b (by linarith)] at hi
  linarith

theorem prime_weighted_transfer_density_right (φ f : ℝ → ℝ) (a b : ℝ)
    (ha : 2 ≤ a) (hab : a ≤ b) (hφa : 0 ≤ φ a)
    (hφ : ContinuousOn φ (Icc a b)) (hf : IntervalIntegrable f volume a b)
    (hf0 : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hd : ∀ x ∈ Ioo a b, HasDerivWithinAt φ (f x) (Ioi x) x) :
    (∑ p ∈ intervalPrimes a b, φ (p : ℝ) *
      (PrimeEulerMass.weight p / primeEuler b)) ≤
      φ b * (PrimeEulerDimensionOne.errorConstant / Real.log b) +
        ∫ t in a..b, φ t * tailDensity t b := by
  have hrepr : ∀ p ∈ intervalPrimes a b,
      φ (p:ℝ) = φ a + ∫ t in a..(p:ℝ), f t := by
    intro p hp
    have hpa := ((mem_intervalPrimes a b p).mp hp).2.2
    have hpb := ((mem_intervalPrimes a b p).mp hp).2.1
    have hsub : Icc a (p:ℝ) ⊆ Icc a b := fun t ht => ⟨ht.1, ht.2.trans hpb.le⟩
    have hfi : IntervalIntegrable f volume a (p:ℝ) :=
      hf.mono_set (by simpa only [uIcc_of_le hab, uIcc_of_le hpa] using hsub)
    have hi := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hpa
      (hφ.mono hsub) (fun t ht => hd t ⟨ht.1, ht.2.trans hpb⟩) hfi
    linarith
  calc
    _ ≤ φ a * tailBound a b + ∫ t in a..b, f t * tailBound t b :=
      prime_weighted_transfer_of_integral φ f a b ha hab hφa hf hf0 hrepr
    _ = _ := tail_integration_by_parts_right φ f a b ha hab hφ hf hd

run_cmd do
  for decl in [``tail_integration_by_parts_right, ``prime_weighted_transfer_density_right] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end PrimeEulerRightTransfer
end
