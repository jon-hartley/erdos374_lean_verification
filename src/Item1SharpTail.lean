import Item1FinitePolynomialTail

/-! UNCOMPILED, October 2, 2026. Exact sharp multiplier, its elementary bound,
independent tail integrability, and a complete finite-polynomial high tail.
The prime-polynomial cap is NOT needed in this frequency range. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Item1SharpTail
open Item1FinitePolynomialTail Item1CountableTail

/-- q^(1+it) is written exp((1+it)*log q), with q>0 at every use. -/
def multiplier (eta t : ℝ) : ℂ :=
  (1-Complex.exp ((1+Complex.I*(t:ℂ))*(Real.log (1-eta):ℂ))) /
    ((eta:ℂ)*(1+Complex.I*(t:ℂ)))

theorem measurable_multiplier (eta : ℝ) : Measurable (multiplier eta) := by
  unfold multiplier
  fun_prop

theorem numerator_bound (eta t : ℝ) (he0 : 0 < eta) (he1 : eta ≤ 1/2) :
    ‖1-Complex.exp ((1+Complex.I*(t:ℂ))*(Real.log (1-eta):ℂ))‖ ≤ 2 := by
  have hq : 0 < 1-eta := by linarith
  have hn : ‖Complex.exp ((1+Complex.I*(t:ℂ))*(Real.log (1-eta):ℂ))‖ = 1-eta := by
    rw [Complex.norm_exp]
    simpa using Real.exp_log hq
  have h := norm_sub_le (1:ℂ)
    (Complex.exp ((1+Complex.I*(t:ℂ))*(Real.log (1-eta):ℂ)))
  rw [norm_one, hn] at h
  linarith

theorem multiplier_bound (eta t : ℝ) (he0 : 0 < eta) (he1 : eta ≤ 1/2)
    (ht : t ≠ 0) : ‖multiplier eta t‖ ≤ 2/(eta*|t|) := by
  have ht0 : 0 < |t| := abs_pos.mpr ht
  have hz : |t| ≤ ‖(1:ℂ)+Complex.I*(t:ℂ)‖ := by
    simpa using Complex.abs_im_le_norm ((1:ℂ)+Complex.I*(t:ℂ))
  have hden : eta*|t| ≤ ‖(eta:ℂ)*((1:ℂ)+Complex.I*(t:ℂ))‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he0]
    exact mul_le_mul_of_nonneg_left hz he0.le
  have hdp : 0 < ‖(eta:ℂ)*((1:ℂ)+Complex.I*(t:ℂ))‖ :=
    (mul_pos he0 ht0).trans_le hden
  unfold multiplier
  rw [norm_div]
  exact (div_le_div_of_nonneg_right (numerator_bound eta t he0 he1) hdp.le).trans
    (div_le_div_of_nonneg_left (by norm_num) (mul_pos he0 ht0) hden)

theorem multiplied_square_bound (F : ℝ → ℂ) (eta t : ℝ)
    (he0 : 0 < eta) (he1 : eta ≤ 1/2) (ht : t ≠ 0) :
    ‖multiplier eta t*F t‖^2 ≤ (4/eta^2)*(‖F t‖^2/t^2) := by
  have h := pow_le_pow_left₀ (norm_nonneg (multiplier eta t))
    (multiplier_bound eta t he0 he1 ht) 2
  have hm := mul_le_mul_of_nonneg_right h (sq_nonneg ‖F t‖)
  rw [norm_mul, mul_pow]
  convert hm using 1 <;> simp only [div_pow, mul_pow, sq_abs] <;> ring

/-- General domination helper; the sharp multiplier is explicit, not a cap hypothesis. -/
theorem sharp_integrable (F : ℝ → ℂ) (eta H : ℝ)
    (he0 : 0 < eta) (he1 : eta ≤ 1/2) (hH : 0 < H)
    (hF : Measurable F)
    (hi : IntegrableOn (fun t => ‖F t‖^2/t^2) (outside H)) :
    IntegrableOn (fun t => ‖multiplier eta t*F t‖^2) (outside H) := by
  apply (hi.const_mul (4/eta^2)).mono'
    (((measurable_multiplier eta).mul hF).norm.pow_const 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (outside_measurable H)] with t ht
  have ht0 : t ≠ 0 := by
    intro he
    have hh : H < |t| := ht
    simp only [he, abs_zero] at hh
    linarith
  change ‖(‖multiplier eta t*F t‖^2 : ℝ)‖ ≤ (4/eta^2)*(‖F t‖^2/t^2)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖multiplier eta t*F t‖)]
  exact multiplied_square_bound F eta t he0 he1 ht0

theorem sharp_integral_le (F : ℝ → ℂ) (eta H : ℝ)
    (he0 : 0 < eta) (he1 : eta ≤ 1/2) (hH : 0 < H)
    (hF : Measurable F)
    (hi : IntegrableOn (fun t => ‖F t‖^2/t^2) (outside H)) :
    (∫ t in outside H, ‖multiplier eta t*F t‖^2) ≤
      (4/eta^2)*(∫ t in outside H, ‖F t‖^2/t^2) := by
  have hm := setIntegral_mono_on (sharp_integrable F eta H he0 he1 hH hF hi)
    (hi.const_mul (4/eta^2)) (outside_measurable H) (by
      intro t ht
      have ht0 : t ≠ 0 := by
        intro he
        have hh : H < |t| := ht
        simp only [he, abs_zero] at hh
        linarith
      exact multiplied_square_bound F eta t he0 he1 ht0)
  simpa only [integral_const_mul] using hm

/-- The full infinite tail. Only finite support and width/height inequalities
are arguments; no interval mean or tail integral is postulated. -/
theorem polynomial_sharp_tail (s : Finset ℕ) (b : ℕ → ℝ) (N : ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ N) (eta H : ℝ)
    (he0 : 0 < eta) (he1 : eta ≤ 1/2) (hH : 1 ≤ H) :
    (∫ t in outside H, ‖multiplier eta t*polynomial s b t‖^2) ≤
      16*energy s b/(eta^2*H)+32*rowCost N*energy s b/(3*eta^2*H^2) := by
  have hi := Item1FinitePolynomialTail.weighted_integrable s b H hH
  have hm := sharp_integral_le (polynomial s b) eta H he0 he1 (by linarith)
    (continuous_polynomial s b).measurable hi
  have hb := mul_le_mul_of_nonneg_left (two_sided_tail s b N hs H hH)
    (show 0 ≤ 4/eta^2 by positivity)
  calc
    _ ≤ (4/eta^2)*(∫ t in outside H, ‖polynomial s b t‖^2/t^2) := hm
    _ ≤ (4/eta^2)*(4*energy s b/H+8*rowCost N*energy s b/(3*H^2)) := hb
    _ = _ := by ring

end Item1SharpTail

-- ROOT SOURCE RECURSIVE AUDIT: exact original declarations.
run_cmd do
  for target in [
    ``Item1SharpTail.measurable_multiplier,
    ``Item1SharpTail.numerator_bound,
    ``Item1SharpTail.multiplier_bound,
    ``Item1SharpTail.multiplied_square_bound,
    ``Item1SharpTail.sharp_integrable,
    ``Item1SharpTail.sharp_integral_le,
    ``Item1SharpTail.polynomial_sharp_tail] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1SharpTail: 7 original theorem guards passed."
