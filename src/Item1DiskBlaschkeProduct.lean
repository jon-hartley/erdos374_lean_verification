import Item1FiniteZeroCharges
import Mathlib.Analysis.Complex.CanonicalDecomposition

/-!
Finite Blaschke products with NATURAL multiplicities.
Only interior zeros occur in the product. Boundary zeros will be allowed to remain
in the analytic factor. This is important: the remaining factor is required to be
nonzero on the OPEN disk, not on its boundary.
-/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
open Set Metric Complex Filter
open scoped BigOperators ComplexConjugate Topology
namespace Item1DiskBlaschkeProduct
open Item1FiniteZeroCharges

/-- The multiplicity function is never replaced by an indicator of the root set. -/
def product (S : Finset ℂ) (m : ℂ → ℕ) (R : ℝ) (z : ℂ) : ℂ :=
  ∏ a ∈ S, blaschke R a z ^ m a

theorem reciprocal_canonical (R : ℝ) (a z : ℂ) :
    (canonicalFactor R a z)⁻¹ = blaschke R a z := by
  simp only [canonicalFactor_apply, blaschke, inv_div]

/-- Denominators stay nonzero on the WHOLE closed disk for an interior root. -/
theorem denominator_ne_zero (R : ℝ) (a z : ℂ)
    (hR : 0 < R) (ha : ‖a‖ < R) (hz : ‖z‖ ≤ R) :
    (R:ℂ)^2 - conj a*z ≠ 0 := by
  have hprod : ‖conj a*z‖ < ‖(R:ℂ)^2‖ := by
    rw [norm_mul, Complex.norm_conj, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    calc
      ‖a‖*‖z‖ ≤ ‖a‖*R := mul_le_mul_of_nonneg_left hz (norm_nonneg a)
      _ < R^2 := by nlinarith
  intro he
  have heq : (R:ℂ)^2 = conj a*z := sub_eq_zero.mp he
  rw [heq] at hprod
  exact (lt_irrefl _ hprod)

theorem blaschke_analytic_closed (R : ℝ) (a : ℂ)
    (hR : 0 < R) (ha : ‖a‖ < R) :
    AnalyticOnNhd ℂ (blaschke R a) (closedBall 0 R) := by
  intro z hz
  have hz' : ‖z‖ ≤ R := by simpa using hz
  unfold blaschke
  exact (analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).div
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
    (denominator_ne_zero R a z hR ha hz')

theorem product_analytic_closed (S : Finset ℂ) (m : ℂ → ℕ) (R : ℝ)
    (hR : 0 < R) (ha : ∀ a ∈ S, ‖a‖ < R) :
    AnalyticOnNhd ℂ (product S m R) (closedBall 0 R) := by
  intro z hz
  unfold product
  exact Finset.analyticAt_fun_prod S (fun a haS =>
    ((blaschke_analytic_closed R a hR (ha a haS)) z hz).pow (m a))

theorem blaschke_norm_boundary (R : ℝ) (a z : ℂ)
    (ha : ‖a‖ < R) (hz : ‖z‖ = R) : ‖blaschke R a z‖ = 1 := by
  rw [←reciprocal_canonical, norm_inv,
    norm_canonicalFactor_eval_circle_eq_one (by simpa using ha) (by simpa using hz)]
  norm_num

theorem product_norm_boundary (S : Finset ℂ) (m : ℂ → ℕ) (R : ℝ)
    (ha : ∀ a ∈ S, ‖a‖ < R) (z : ℂ) (hz : ‖z‖ = R) :
    ‖product S m R z‖ = 1 := by
  unfold product
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro a haS
  rw [norm_pow, blaschke_norm_boundary R a z (ha a haS) hz, one_pow]

theorem product_norm_center_le_one (S : Finset ℂ) (m : ℂ → ℕ) (R : ℝ)
    (hR : 0 < R) (ha : ∀ a ∈ S, ‖a‖ < R) :
    ‖product S m R 0‖ ≤ 1 := by
  unfold product
  rw [norm_prod]
  apply Finset.prod_le_one₀
  · intro a _; exact norm_nonneg _
  · intro a haS
    rw [norm_pow, blaschke_zero R a hR.ne', norm_div, norm_neg,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    exact pow_le_one₀ (div_nonneg (norm_nonneg a) hR.le)
      ((div_le_one hR).mpr (ha a haS).le)

theorem product_center_ne_zero (S : Finset ℂ) (m : ℂ → ℕ) (R : ℝ)
    (hR : R ≠ 0) (ha : ∀ a ∈ S, a ≠ 0) :
    product S m R 0 ≠ 0 := by
  unfold product
  exact Finset.prod_ne_zero_iff.mpr (fun a haS =>
    pow_ne_zero _ (blaschke_zero_ne R a hR (ha a haS)))

/-- Every zero contributes its full multiplicity to the logarithmic derivative. -/
theorem product_logDeriv_center (S : Finset ℂ) (m : ℂ → ℕ) (R : ℝ)
    (hR : R ≠ 0) (ha : ∀ a ∈ S, a ≠ 0) :
    logDeriv (product S m R) 0 =
      ∑ a ∈ S, (m a:ℂ) * logDeriv (blaschke R a) 0 := by
  unfold product
  rw [logDeriv_fun_prod (f := fun (a z : ℂ) => blaschke R a z ^ m a)
    (fun a haS => pow_ne_zero _ (blaschke_zero_ne R a hR (ha a haS)))
    (fun a _ => (blaschke_differentiable_zero R a hR).pow (m a))]
  apply Finset.sum_congr rfl
  intro a _
  exact logDeriv_fun_pow (blaschke_differentiable_zero R a hR) (m a)

theorem product_logDeriv_re (S : Finset ℂ) (m : ℂ → ℕ) (R : ℝ)
    (hR : R ≠ 0) (ha : ∀ a ∈ S, a ≠ 0) :
    (logDeriv (product S m R) 0).re =
      ∑ a ∈ S, (m a:ℝ) * charge R a := by
  rw [product_logDeriv_center S m R hR ha, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a haS
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero, logDeriv_blaschke_re R a hR (ha a haS)]

end Item1DiskBlaschkeProduct

run_cmd do
  for target in [``Item1DiskBlaschkeProduct.reciprocal_canonical,
    ``Item1DiskBlaschkeProduct.denominator_ne_zero,
    ``Item1DiskBlaschkeProduct.blaschke_analytic_closed,
    ``Item1DiskBlaschkeProduct.product_analytic_closed,
    ``Item1DiskBlaschkeProduct.blaschke_norm_boundary,
    ``Item1DiskBlaschkeProduct.product_norm_boundary,
    ``Item1DiskBlaschkeProduct.product_norm_center_le_one,
    ``Item1DiskBlaschkeProduct.product_center_ne_zero,
    ``Item1DiskBlaschkeProduct.product_logDeriv_center,
    ``Item1DiskBlaschkeProduct.product_logDeriv_re] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Item1DiskBlaschkeProduct.reciprocal_canonical
#print axioms Item1DiskBlaschkeProduct.denominator_ne_zero
#print axioms Item1DiskBlaschkeProduct.blaschke_analytic_closed
#print axioms Item1DiskBlaschkeProduct.product_analytic_closed
#print axioms Item1DiskBlaschkeProduct.blaschke_norm_boundary
#print axioms Item1DiskBlaschkeProduct.product_norm_boundary
#print axioms Item1DiskBlaschkeProduct.product_norm_center_le_one
#print axioms Item1DiskBlaschkeProduct.product_center_ne_zero
#print axioms Item1DiskBlaschkeProduct.product_logDeriv_center
#print axioms Item1DiskBlaschkeProduct.product_logDeriv_re
