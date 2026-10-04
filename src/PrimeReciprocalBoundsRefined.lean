import PrimeReciprocalBounds

/-! The same unconditional Chebyshev/Abel argument with leading constant two.
This module reuses the checked summation identity and endpoint correction. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter MeasureTheory PrimeReciprocalBounds

namespace PrimeReciprocalBoundsRefined

theorem log_four_le : Real.log 4 ≤ (7 : ℝ)/4 := by
  have hs : Real.sqrt 2 ≤ (23 : ℝ)/16 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hl := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
  rw [Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hl
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    simpa only [show (2 : ℝ)^2 = 4 by norm_num, Nat.cast_ofNat] using Real.log_pow (2 : ℝ) 2
  rw [h4]
  linarith

theorem reciprocal_openClosed_le_C (C a b : ℝ) (hC : 0 ≤ C)
    (ha : 1 < a) (hab : a ≤ b)
    (hc : ∀ t ∈ Set.Icc a b,
      (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ C*t / Real.log t) :
    ∑ p ∈ openClosedPrimes a b, (p : ℝ)⁻¹ ≤
      C * (Real.log (Real.log b) - Real.log (Real.log a)) + C / Real.log a := by
  have hb : 1 < b := ha.trans_le hab
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hlog : ContinuousOn (fun t : ℝ => t⁻¹ / Real.log t) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    have hn : ∀ t ∈ Set.Icc a b, t ≠ 0 := fun t ht => ne_of_gt (ha0.trans_le ht.1)
    exact (continuousOn_id.inv₀ hn).div (continuousOn_id.log hn)
      (fun t ht => ne_of_gt (Real.log_pos (ha.trans_le ht.1)))
  have hi := intervalIntegral.integral_mono_on hab
    (count_inv_sq_integrable a b ha hab) (hlog.const_mul C).intervalIntegrable
    (fun t ht => show (t^2)⁻¹ * (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤
      C * (t⁻¹ / Real.log t) from calc
        _ ≤ (t^2)⁻¹ * (C*t / Real.log t) :=
          mul_le_mul_of_nonneg_left (hc t ht) (by positivity)
        _ = _ := by
          have ht0 : t ≠ 0 := by linarith [ht.1]
          field_simp)
  rw [intervalIntegral.integral_const_mul, integral_inv_div_log ha hb] at hi
  have hleft : 0 ≤ a⁻¹ * (Nat.primeCounting ⌊a⌋₊ : ℝ) := by positivity
  have hright : b⁻¹ * (Nat.primeCounting ⌊b⌋₊ : ℝ) ≤ C / Real.log b := calc
    _ ≤ b⁻¹ * (C*b / Real.log b) :=
      mul_le_mul_of_nonneg_left (hc b ⟨hab, le_rfl⟩) (by positivity)
    _ = _ := by field_simp
  have hinv : C / Real.log b ≤ C / Real.log a :=
    div_le_div_of_nonneg_left hC (Real.log_pos ha) (Real.log_le_log ha0 hab)
  rw [reciprocal_abel a b ha hab]
  linarith

theorem eventual_primeCounting_bound_two :
    ∃ W : ℝ, 2 ≤ W ∧ ∀ x : ℝ, W ≤ x →
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ 2*x / Real.log x := by
  obtain ⟨W, hW⟩ := eventually_atTop.1
    (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1/4))
  refine ⟨max 2 W, le_max_left _ _, fun x hx => ?_⟩
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  refine (hW x ((le_max_right _ _).trans hx)).trans ?_
  apply div_le_div_of_nonneg_right _ hlog.le
  apply mul_le_mul_of_nonneg_right _ (by linarith)
  linarith [log_four_le]

theorem eventual_reciprocal_interval_bound_two :
    ∃ W : ℝ, 2 ≤ W ∧ ∀ (a b : ℝ) (S : Finset ℕ), W ≤ a → a ≤ b →
      (∀ p ∈ S, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b) →
      ∑ p ∈ S, (p : ℝ)⁻¹ ≤
        2 * Real.log (Real.log b / Real.log a) + 3 / Real.log a := by
  obtain ⟨W, hW2, hW⟩ := eventual_primeCounting_bound_two
  refine ⟨W, hW2, fun a b S ha hab hS => ?_⟩
  have ha1 : 1 < a := by linarith
  have hb1 : 1 < b := ha1.trans_le hab
  have hi := reciprocal_openClosed_le_C 2 a b (by norm_num) ha1 hab
    (fun t ht => hW t (ha.trans ht.1))
  have hs := sum_le_openClosed_add S a b ha1 hS
  rw [Real.log_div (ne_of_gt (Real.log_pos hb1)) (ne_of_gt (Real.log_pos ha1))]
  simp only [div_eq_mul_inv] at hi hs ⊢
  linarith

theorem eventual_reciprocal_geometric_bound_two :
    ∃ W : ℝ, 2 ≤ W ∧ ∀ (u a q : ℝ) (S : Finset ℕ), W ≤ u → u ≤ a → 1 ≤ q →
      (∀ p ∈ S, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ a^q) →
      ∑ p ∈ S, (p : ℝ)⁻¹ ≤ 2 * Real.log q + 3 / Real.log u := by
  obtain ⟨W, hW2, hW⟩ := eventual_reciprocal_interval_bound_two
  refine ⟨W, hW2, fun u a q S hu hua hq hS => ?_⟩
  have hu1 : 1 < u := by linarith
  have ha1 : 1 < a := hu1.trans_le hua
  have haa : a ≤ a^q := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le ha1.le hq
  have hi := hW a (a^q) S (hu.trans hua) haa hS
  rw [Real.log_rpow (by linarith : 0 < a), mul_div_cancel_right₀ _
    (ne_of_gt (Real.log_pos ha1))] at hi
  have hinv : 3 / Real.log a ≤ 3 / Real.log u :=
    div_le_div_of_nonneg_left (by norm_num) (Real.log_pos hu1)
      (Real.log_le_log (by linarith) hua)
  linarith

#print axioms eventual_reciprocal_geometric_bound_two
run_cmd do
  for decl in [``log_four_le, ``reciprocal_openClosed_le_C,
    ``eventual_primeCounting_bound_two, ``eventual_reciprocal_interval_bound_two,
    ``eventual_reciprocal_geometric_bound_two] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end PrimeReciprocalBoundsRefined
end
