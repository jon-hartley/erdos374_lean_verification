import SievePrimeSubsetEvaluation
import SievePrefix

/-! Exact two-part vector lower sieve algebra, including specialization to the
actual recursive prefix selectors. No sieve main term or analytic bound is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open scoped BigOperators

namespace SieveVector

def lowerKernel (l0 u0 l1 u1 : ℝ) : ℝ := l0*u1 + u0*l1 - u0*u1

/-- All three summands are nonnegative for lower/upper brackets of nonnegative models. -/
theorem lowerKernel_gap_identity (l0 u0 l1 u1 g0 g1 : ℝ) :
    g0*g1 - lowerKernel l0 u0 l1 u1 =
      (g0-l0)*u1 + (g1-l1)*u0 + (u0-g0)*(u1-g1) := by
  unfold lowerKernel
  ring

theorem lowerKernel_le_product (l0 u0 l1 u1 g0 g1 : ℝ)
    (hl0 : l0 ≤ g0) (hu0 : g0 ≤ u0) (hl1 : l1 ≤ g1) (hu1 : g1 ≤ u1)
    (hg0 : 0 ≤ g0) (hg1 : 0 ≤ g1) :
    lowerKernel l0 u0 l1 u1 ≤ g0*g1 := by
  have h0 : 0 ≤ u0 := hg0.trans hu0
  have h1 : 0 ≤ u1 := hg1.trans hu1
  have hgap : 0 ≤ g0*g1 - lowerKernel l0 u0 l1 u1 := by
    rw [lowerKernel_gap_identity]
    exact add_nonneg
      (add_nonneg (mul_nonneg (sub_nonneg.mpr hl0) h1)
        (mul_nonneg (sub_nonneg.mpr hl1) h0))
      (mul_nonneg (sub_nonneg.mpr hu0) (sub_nonneg.mpr hu1))
  linarith

theorem product_le_upper (u0 u1 g0 g1 : ℝ)
    (hu0 : g0 ≤ u0) (hu1 : g1 ≤ u1) (hg0 : 0 ≤ g0) (hg1 : 0 ≤ g1) :
    g0*g1 ≤ u0*u1 :=
  mul_le_mul hu0 hu1 hg1 (hg0.trans hu0)

theorem shared_difference_abs_le_one (l u : ℝ) (hl : |l| ≤ 1) (hu : |u| ≤ 1)
    (hs : l = 0 ∨ u = 0 ∨ l = u) : |l-u| ≤ 1 := by
  rcases hs with hs | hs | hs
  · simpa only [hs, zero_sub, abs_neg] using hu
  · simpa only [hs, sub_zero] using hl
  · simp [hs]

/-- Shared parity signs avoid the loss of three from a triangle inequality. -/
theorem lowerKernel_abs_le_one (l0 u0 l1 u1 : ℝ)
    (hl0 : |l0| ≤ 1) (hu0 : |u0| ≤ 1) (hl1 : |l1| ≤ 1) (hu1 : |u1| ≤ 1)
    (hs0 : l0 = 0 ∨ u0 = 0 ∨ l0 = u0)
    (hs1 : l1 = 0 ∨ u1 = 0 ∨ l1 = u1) : |lowerKernel l0 u0 l1 u1| ≤ 1 := by
  rcases hs0 with h0 | h0 | h0
  · have he : lowerKernel l0 u0 l1 u1 = u0*(l1-u1) := by simp [lowerKernel, h0, mul_sub]
    rw [he, abs_mul]
    simpa using mul_le_mul hu0 (shared_difference_abs_le_one l1 u1 hl1 hu1 hs1)
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  · simp only [lowerKernel, h0, zero_mul, add_zero, sub_zero, abs_mul]
    simpa using mul_le_mul hl0 hu1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  · have he : lowerKernel l0 u0 l1 u1 = u0*l1 := by simp [lowerKernel, h0]
    rw [he, abs_mul]
    simpa using mul_le_mul hu0 hl1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

/-- The inputs here are actual collected coefficients from finite prime-subset families. -/
theorem selectedCoefficient_kernel_abs_le_one (A0 B0 A1 B1 : Finset (Finset ℕ))
    (hA0 : ∀ s ∈ A0, ∀ p ∈ s, p.Prime) (hB0 : ∀ s ∈ B0, ∀ p ∈ s, p.Prime)
    (hA1 : ∀ s ∈ A1, ∀ p ∈ s, p.Prime) (hB1 : ∀ s ∈ B1, ∀ p ∈ s, p.Prime)
    (m n : ℕ) :
    |lowerKernel (SievePrimeSubset.selectedCoefficient A0 m)
      (SievePrimeSubset.selectedCoefficient B0 m)
      (SievePrimeSubset.selectedCoefficient A1 n)
      (SievePrimeSubset.selectedCoefficient B1 n)| ≤ 1 := by
  apply lowerKernel_abs_le_one
  · exact SievePrimeSubset.selectedCoefficient_abs_le_one A0 hA0 m
  · exact SievePrimeSubset.selectedCoefficient_abs_le_one B0 hB0 m
  · exact SievePrimeSubset.selectedCoefficient_abs_le_one A1 hA1 n
  · exact SievePrimeSubset.selectedCoefficient_abs_le_one B1 hB1 n
  · exact SievePrimeSubset.selectedCoefficient_shared_sign A0 B0 hA0 hB0 m
  · exact SievePrimeSubset.selectedCoefficient_shared_sign A1 B1 hA1 hB1 n

/-- The vector brackets are consequences of the actual selector recursion,
not pointwise sieve bounds supplied by the caller. -/
theorem prefix_vector_bounds (gate0 gate1 : ℕ → ℕ → Prop) (d0 d1 : ℕ)
    (ps0 ps1 : List ℕ) (b0 b1 : ℕ → ℝ) (hnd0 : ps0.Nodup) (hnd1 : ps1.Nodup)
    (hb0 : ∀ p ∈ ps0, 0 ≤ b0 p ∧ b0 p ≤ 1)
    (hb1 : ∀ p ∈ ps1, 0 ≤ b1 p ∧ b1 p ≤ 1) :
    lowerKernel (SievePrefix.value gate0 false d0 ps0 b0)
        (SievePrefix.value gate0 true d0 ps0 b0)
        (SievePrefix.value gate1 false d1 ps1 b1)
        (SievePrefix.value gate1 true d1 ps1 b1) ≤
      (∏ p ∈ ps0.toFinset, (1-b0 p)) * (∏ p ∈ ps1.toFinset, (1-b1 p)) ∧
    (∏ p ∈ ps0.toFinset, (1-b0 p)) * (∏ p ∈ ps1.toFinset, (1-b1 p)) ≤
      SievePrefix.value gate0 true d0 ps0 b0 * SievePrefix.value gate1 true d1 ps1 b1 := by
  have h0 := SievePrefix.value_bounds gate0 d0 ps0 b0 hnd0 hb0
  have h1 := SievePrefix.value_bounds gate1 d1 ps1 b1 hnd1 hb1
  have hg0 : 0 ≤ ∏ p ∈ ps0.toFinset, (1-b0 p) :=
    Finset.prod_nonneg (fun p hp => sub_nonneg.mpr (hb0 p (List.mem_toFinset.mp hp)).2)
  have hg1 : 0 ≤ ∏ p ∈ ps1.toFinset, (1-b1 p) :=
    Finset.prod_nonneg (fun p hp => sub_nonneg.mpr (hb1 p (List.mem_toFinset.mp hp)).2)
  exact ⟨lowerKernel_le_product _ _ _ _ _ _ h0.1 h0.2 h1.1 h1.2 hg0 hg1,
    product_le_upper _ _ _ _ h0.2 h1.2 hg0 hg1⟩

#print axioms prefix_vector_bounds
#print axioms selectedCoefficient_kernel_abs_le_one
run_cmd do
  for decl in [``lowerKernel_gap_identity, ``lowerKernel_le_product, ``product_le_upper,
      ``shared_difference_abs_le_one, ``lowerKernel_abs_le_one,
      ``selectedCoefficient_kernel_abs_le_one, ``prefix_vector_bounds] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
run_cmd Lean.logInfo "SIEVE_VECTOR_PASSED; ACTUAL PREFIX VALUES; NO QUANTITATIVE MAIN TERM"

end SieveVector
end
