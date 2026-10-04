import Item1ContourIntegralBounds

/-!
UNCOMPILED. The actual smoothed Mangoldt sum is bounded by all pieces of its
translated-zeta contour. PositiveStrip is the single genuine analytic premise.
No raw edge, tail, inversion, Fubini, or smoothed-cap premise is accepted.
The input strip is NOT proved here; this is not an unconditional cap theorem.
-/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
open MeasureTheory Set Filter
namespace Item1SmoothedContourEstimate
open Item1LogRampSmoothing Item1EntireRampKernel Item1RampMellinInversion
open Item1RampDirichlet Item1RightLineBound Item1ShiftedCapRectangle
open Item1ZetaContourGeometry Item1ContourIntegralBounds

/-- Finite rectangle plus the TWO original infinite right-line tails. -/
theorem full_right_integral_bound (N δ a C T₀ t c : ℝ)
    (hN : 1 ≤ N) (hδ : 0 < δ) («hδλ» : δ ≤ Real.log 2)
    (ha : 0 < a) (ha1 : a ≤ 1/2) (hC : 0 ≤ C) (hT : 4 ≤ T₀)
    (ht : 8 ≤ t) (htT : 2*T₀ ≤ t) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hs : PositiveStrip a C T₀) :
    ‖∫ v : ℝ, integrand N δ t (line c v)‖ ≤
      18*Real.pi*C*(heightLog t)^9*Real.exp (-depth a t*Real.log N)/δ +
      144*Real.exp (c*Real.log N)*C*(heightLog t)^9/(δ*t^2) +
      216*Real.exp (c*Real.log N)/(c^2*δ*t) := by
  have hi : Integrable (fun v => integrand N δ t (line c v)) :=
    zeta_right_integrand_integrable N δ t c hδ «hδλ» hc0 hc1
  have hd := integrand_rectangle N δ a C T₀ t c hδ.le ha ha1 hT ht htT hc0 hc1 hs
  have hleft := left_vertical_bound N δ a C T₀ t c hδ «hδλ» ha ha1 hC hT ht htT hc0 hc1 hs
  have htop := horizontal_bound N δ a C T₀ t c (t/2) hN hδ «hδλ»
    ha ha1 hC hT ht htT hc0 hc1 (Or.inl rfl) hs
  have hbot := horizontal_bound N δ a C T₀ t c (-t/2) hN hδ «hδλ»
    ha ha1 hC hT ht htT hc0 hc1 (Or.inr rfl) hs
  have hrect := norm_vertical_of_edges (integrand N δ t) (-depth a t) c (t/2)
    _ _ (by simpa only [neg_div] using hd) hleft htop (by simpa only [neg_div] using hbot)
  have htail := right_tail_bound N δ t c (t/2) hδ «hδλ» hc0 hc1 (by linarith)
  have hmiddle : ‖∫ v in Icc (-t/2) (t/2), integrand N δ t (line c v)‖ =
      ‖vertical (integrand N δ t) c (t/2)‖ := by
    simp only [vertical,norm_mul,Complex.norm_I,one_mul]
    rw [intervalIntegral.integral_of_le (show -(t/2) ≤ t/2 by linarith),
      ←integral_Icc_eq_integral_Ioc]
    simp only [neg_div,line]
  have hsplit := integral_add_compl (s:=Icc (-t/2) (t/2)) measurableSet_Icc hi
  rw [←hsplit]
  have hnorm := norm_add_le (∫ v in Icc (-t/2) (t/2), integrand N δ t (line c v))
    (∫ v in (Icc (-t/2) (t/2))ᶜ, integrand N δ t (line c v))
  rw [hmiddle] at hnorm
  have htailnorm : ‖∫ v in (Icc (-t/2) (t/2))ᶜ, integrand N δ t (line c v)‖ ≤
      108*Real.exp (c*Real.log N)/(c^2*δ*(t/2)) := by
    exact (norm_integral_le_integral_norm _).trans (by simpa only [tails,neg_div] using htail)
  apply hnorm.trans
  have hh := add_le_add hrect htailnorm
  convert hh using 1 <;> field_simp <;> ring

/-- The exact smoothed-sum estimate, before fixing the real contour offset.
Its premise is about the genuine logarithmic derivative, not this finite sum. -/
theorem smoothed_bound_of_strip (N δ a C T₀ t c : ℝ)
    (hN : 1 ≤ N) (hδ : 0 < δ) («hδλ» : δ ≤ Real.log 2)
    (ha : 0 < a) (ha1 : a ≤ 1/2) (hC : 0 ≤ C) (hT : 4 ≤ T₀)
    (ht : 8 ≤ t) (htT : 2*T₀ ≤ t) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hs : PositiveStrip a C T₀) :
    ‖smoothFinite N δ t‖ ≤
      9*C*(heightLog t)^9*Real.exp (-depth a t*Real.log N)/δ +
      72*Real.exp (c*Real.log N)*C*(heightLog t)^9/(δ*t^2) +
      108*Real.exp (c*Real.log N)/(c^2*δ*t) := by
  have hR : 0 ≤ heightLog t := (heightLog_pos t ht).le
  have hfull := full_right_integral_bound N δ a C T₀ t c
    hN hδ «hδλ» ha ha1 hC hT ht htT hc0 hc1 hs
  have hpi : 1 ≤ Real.pi := by linarith [Real.one_le_pi_div_two]
  have hpositive : 0 ≤ 1/(2*Real.pi) := by positivity
  rw [smoothed_zeta_identity N δ t c (by linarith) hδ «hδλ» hc0 hc1,
    norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hpositive]
  change (1/(2*Real.pi))*‖∫ v : ℝ, integrand N δ t (line c v)‖ ≤ _
  apply (mul_le_mul_of_nonneg_left hfull hpositive).trans
  have heq : (1/(2*Real.pi)) *
      (18*Real.pi*C*(heightLog t)^9*Real.exp (-depth a t*Real.log N)/δ +
       144*Real.exp (c*Real.log N)*C*(heightLog t)^9/(δ*t^2) +
       216*Real.exp (c*Real.log N)/(c^2*δ*t)) =
      9*C*(heightLog t)^9*Real.exp (-depth a t*Real.log N)/δ +
       (72*Real.exp (c*Real.log N)*C*(heightLog t)^9/(δ*t^2))/Real.pi +
       (108*Real.exp (c*Real.log N)/(c^2*δ*t))/Real.pi := by
    field_simp
    <;> ring
  rw [heq]
  exact add_le_add
    (add_le_add le_rfl (div_le_self (by positivity) hpi))
    (div_le_self (by positivity) hpi)

/-- Specialize to c=1/log N and pay exp(1) by 3. This is the three-term
smoothed envelope in the prior written argument, with every integral filled. -/
theorem smoothed_bound_log_choice (N δ a C T₀ t : ℝ)
    (hN : 0 < N) (hlog : 2 ≤ Real.log N)
    (hδ : 0 < δ) («hδλ» : δ ≤ Real.log 2)
    (ha : 0 < a) (ha1 : a ≤ 1/2) (hC : 0 ≤ C) (hT : 4 ≤ T₀)
    (ht : 8 ≤ t) (htT : 2*T₀ ≤ t) (hs : PositiveStrip a C T₀) :
    ‖smoothFinite N δ t‖ ≤
      9*C*(heightLog t)^9*Real.exp (-a*Real.log N/(heightLog t)^(3/4:ℝ))/δ +
      216*C*(heightLog t)^9/(δ*t^2) +
      324*(Real.log N)^2/(δ*t) := by
  have hR : 0 ≤ heightLog t := (heightLog_pos t ht).le
  have hlp : 0 < Real.log N := by linarith
  have hN1 : 1 ≤ N := by
    rw [←Real.exp_log hN]
    exact Real.one_le_exp_iff.mpr hlp.le
  have hc0 : 0 < 1/Real.log N := by positivity
  have hc1 : 1/Real.log N ≤ 1 := (div_le_one hlp).mpr (by linarith)
  have hh := smoothed_bound_of_strip N δ a C T₀ t (1/Real.log N)
    hN1 hδ «hδλ» ha ha1 hC hT ht htT hc0 hc1 hs
  have hexp : Real.exp ((1/Real.log N)*Real.log N) ≤ 3 := by
    rw [one_div_mul_cancel hlp.ne']
    exact le_of_lt (lt_of_lt_of_le Real.exp_one_lt_d9 (by norm_num))
  have hfirst : -depth a t*Real.log N = -a*Real.log N/(heightLog t)^(3/4:ℝ) := by
    unfold depth
    ring
  rw [hfirst] at hh
  have hsecond : 72*Real.exp ((1/Real.log N)*Real.log N)*C*(heightLog t)^9/(δ*t^2) ≤
      216*C*(heightLog t)^9/(δ*t^2) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right hexp (show 0 ≤ C*(heightLog t)^9 by positivity)]
  have hthird : 108*Real.exp ((1/Real.log N)*Real.log N)/((1/Real.log N)^2*δ*t) ≤
      324*(Real.log N)^2/(δ*t) := by
    have hnorm : 108*Real.exp ((1/Real.log N)*Real.log N)/((1/Real.log N)^2*δ*t) =
        108*Real.exp ((1/Real.log N)*Real.log N)*(Real.log N)^2/(δ*t) := by
      field_simp
      <;> ring
    rw [hnorm]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right hexp (sq_nonneg (Real.log N))]
  exact hh.trans (add_le_add (add_le_add le_rfl hsecond) hthird)

end Item1SmoothedContourEstimate

run_cmd do
  for target in [
    ``Item1SmoothedContourEstimate.full_right_integral_bound,
    ``Item1SmoothedContourEstimate.smoothed_bound_of_strip,
    ``Item1SmoothedContourEstimate.smoothed_bound_log_choice] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Item1SmoothedContourEstimate.smoothed_bound_log_choice

