import MangoldtReciprocal
import PrimeReciprocalBounds

/-! A global dimension-one reciprocal-prime interval bound.  The leading
constant is exactly one.  Prime powers are retained as nonnegative terms in
the elementary Mangoldt partial-summation majorant, so no PNT is needed. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators ArithmeticFunction.vonMangoldt
open MeasureTheory

namespace MertensPrimeInterval
open MangoldtReciprocal PrimeReciprocalBounds

theorem kernel_continuous (a b : ℝ) (ha : 1 < a) :
    ContinuousOn (fun t : ℝ => t⁻¹ / (Real.log t)^2) (Set.Icc a b) := by
  have hn : ∀ t ∈ Set.Icc a b, t ≠ 0 := fun t ht => by linarith [ht.1]
  have hl : ∀ t ∈ Set.Icc a b, Real.log t ≠ 0 :=
    fun t ht => ne_of_gt (Real.log_pos (ha.trans_le ht.1))
  exact (continuousOn_id.inv₀ hn).div ((continuousOn_id.log hn).pow 2)
    (fun t ht => pow_ne_zero 2 (hl t ht))

theorem mangoldt_log_abel (a b : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (Real.log n)⁻¹ * coefficient n) =
      (Real.log b)⁻¹ * mass b - (Real.log a)⁻¹ * mass a +
        ∫ t in a..b, (t⁻¹ / (Real.log t)^2) * mass t := by
  have h := sum_mul_eq_sub_sub_integral_mul coefficient
    (f := fun t : ℝ => (Real.log t)⁻¹) (by linarith : 0 ≤ a) hab
    (fun t ht => (Real.hasDerivAt_inv_log (by linarith [ht.1])
      (by linarith [ht.1]) (by linarith [ht.1])).differentiableAt)
    (by simpa only [Real.deriv_inv_log, neg_div, Pi.neg_apply] using!
      (kernel_continuous a b ha).neg.integrableOn_Icc)
  simp only [sum_coefficient_Icc, Real.deriv_inv_log, neg_div, neg_mul,
    ← intervalIntegral.integral_of_le hab] at h
  simpa only [intervalIntegral.integral_neg, sub_neg_eq_add] using h

theorem kernel_mass_integrable (a b : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun t : ℝ => (t⁻¹ / (Real.log t)^2) * mass t) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  simpa only [sum_coefficient_Icc] using
    integrableOn_mul_sum_Icc coefficient (m := 0) (by linarith : 0 ≤ a)
      (kernel_continuous a b ha).integrableOn_Icc

theorem mangoldt_log_interval_le (a b : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (Real.log n)⁻¹ * coefficient n) ≤
      Real.log (Real.log b) - Real.log (Real.log a) + 9 / Real.log a := by
  have hb : 1 < b := ha.trans_le hab
  have hla : 0 < Real.log a := Real.log_pos ha
  have hlb : 0 < Real.log b := Real.log_pos hb
  have hn : ∀ t ∈ Set.Icc a b, t ≠ 0 := fun t ht => by linarith [ht.1]
  have hl : ∀ t ∈ Set.Icc a b, Real.log t ≠ 0 :=
    fun t ht => ne_of_gt (Real.log_pos (ha.trans_le ht.1))
  have hlog : ContinuousOn (fun t : ℝ => t⁻¹ / Real.log t) (Set.Icc a b) :=
    (continuousOn_id.inv₀ hn).div (continuousOn_id.log hn) hl
  have hI1 : IntervalIntegrable (fun t : ℝ => t⁻¹ / Real.log t) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hlog.integrableOn_Icc
  have hI2 : IntervalIntegrable (fun t : ℝ => t⁻¹ / (Real.log t)^2) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact (kernel_continuous a b ha).integrableOn_Icc
  have hi := intervalIntegral.integral_mono_on hab (kernel_mass_integrable a b ha hab)
    (hI1.add (hI2.const_mul 7)) (fun t ht => show
      (t⁻¹ / (Real.log t)^2) * mass t ≤
        t⁻¹ / Real.log t + 7 * (t⁻¹ / (Real.log t)^2) from calc
      _ ≤ (t⁻¹ / (Real.log t)^2) * (Real.log t + 7) :=
        mul_le_mul_of_nonneg_left (mass_bounds t (by linarith [ht.1])).2
          (by
            have ht0 : 0 < t := by linarith [ht.1]
            exact div_nonneg (inv_nonneg.mpr ht0.le) (sq_nonneg _))
      _ = _ := by field_simp [hl t ht])
  rw [intervalIntegral.integral_add hI1 (hI2.const_mul 7),
    intervalIntegral.integral_const_mul, integral_inv_div_log ha hb,
    integral_inv_div_log_sq ha hb] at hi
  have hu : (Real.log b)⁻¹ * mass b ≤ 1 + 7 / Real.log b := calc
    _ ≤ (Real.log b)⁻¹ * (Real.log b + 7) :=
      mul_le_mul_of_nonneg_left (mass_bounds b hb.le).2 (by positivity)
    _ = _ := by field_simp
  have hlower : 1 - 2 / Real.log a ≤ (Real.log a)⁻¹ * mass a := calc
    _ = (Real.log a)⁻¹ * (Real.log a - 2) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (mass_bounds a ha.le).1 (by positivity)
  rw [mangoldt_log_abel a b ha hab]
  simp only [div_eq_mul_inv] at hi hu hlower ⊢
  linarith

theorem prime_openClosed_le_mangoldt (a b : ℝ) :
    (∑ p ∈ openClosedPrimes a b, (p : ℝ)⁻¹) ≤
      ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (Real.log n)⁻¹ * coefficient n := by
  calc
    _ = ∑ p ∈ openClosedPrimes a b, (Real.log p)⁻¹ * coefficient p := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpp := (Finset.mem_filter.mp hp).2
      have hlog : Real.log p ≠ 0 :=
        ne_of_gt (Real.log_pos (by exact_mod_cast hpp.one_lt))
      rw [coefficient, ArithmeticFunction.vonMangoldt_apply_prime hpp]
      field_simp
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun n hn _ => by
        have hn1 : (1 : ℝ) ≤ n := by
          exact_mod_cast Nat.succ_le_of_lt
            ((Nat.zero_le ⌊a⌋₊).trans_lt (Finset.mem_Ioc.mp hn).1)
        exact mul_nonneg (inv_nonneg.mpr (Real.log_nonneg hn1)) (coefficient_nonneg n))

/-- Every finite set of actual primes in the closed interval satisfies a
dimension-one bound.  There is no unproved arithmetic premise or threshold. -/
theorem prime_reciprocal_interval (a b : ℝ) (S : Finset ℕ)
    (ha : 1 < a) (hab : a ≤ b)
    (hS : ∀ p ∈ S, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b) :
    ∑ p ∈ S, (p : ℝ)⁻¹ ≤
      Real.log (Real.log b / Real.log a) + 10 / Real.log a := by
  have hsub := sum_le_openClosed_add S a b ha hS
  have hprime := prime_openClosed_le_mangoldt a b
  have hM := mangoldt_log_interval_le a b ha hab
  rw [Real.log_div (ne_of_gt (Real.log_pos (ha.trans_le hab)))
    (ne_of_gt (Real.log_pos ha))]
  simp only [div_eq_mul_inv] at hsub hM ⊢
  linarith

theorem prime_reciprocal_geometric (u a q : ℝ) (S : Finset ℕ)
    (hu : 1 < u) (hua : u ≤ a) (hq : 1 ≤ q)
    (hS : ∀ p ∈ S, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ a^q) :
    ∑ p ∈ S, (p : ℝ)⁻¹ ≤ Real.log q + 10 / Real.log u := by
  have ha : 1 < a := hu.trans_le hua
  have haa : a ≤ a^q := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le ha.le hq
  have h := prime_reciprocal_interval a (a^q) S ha haa hS
  rw [Real.log_rpow (by linarith : 0 < a),
    mul_div_cancel_right₀ _ (ne_of_gt (Real.log_pos ha))] at h
  have hi : 10 / Real.log a ≤ 10 / Real.log u :=
    div_le_div_of_nonneg_left (by norm_num) (Real.log_pos hu)
      (Real.log_le_log (by linarith) hua)
  linarith

#print axioms prime_reciprocal_interval
run_cmd do
  for decl in [``kernel_continuous, ``mangoldt_log_abel, ``kernel_mass_integrable,
    ``mangoldt_log_interval_le, ``prime_openClosed_le_mangoldt,
    ``prime_reciprocal_interval, ``prime_reciprocal_geometric] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end MertensPrimeInterval
end
