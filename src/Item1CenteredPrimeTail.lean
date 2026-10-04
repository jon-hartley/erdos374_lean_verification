import Item1CollectedPrimeTail

/-! UNCOMPILED. The reference uses TWO FULL real reciprocal-coefficient
polynomials, independently of the selected all-prime tuple set. It is therefore
compatible with the original full-Mangoldt center; it does not silently recenter.
The third reference factor is written in logarithmic coordinates. Its equality
with the existing sigma-one integral must be matched in the maintained project.
-/
set_option autoImplicit false
set_option maxHeartbeats 18000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Item1CenteredPrimeTail
open Item1CountableTail Item1FinitePolynomialTail Item1SharpTail Item1CollectedPrimeTail
open Item1PrimeTripleFibers Erdos374.HarmanAnalytic151MeanSquare

def referenceFactor (a b t : ℝ) : ℂ := ∫ u in a..b, exponentialKernel151 (-t) u

def mixedReference (A B : Finset ℕ) (c d : ℕ → ℝ) (a b t : ℝ) : ℂ :=
  polynomial A c t*polynomial B d t*referenceFactor a b t

theorem referenceFactor_formula (a b t : ℝ) :
    referenceFactor a b t = if t=0 then ((b-a:ℝ):ℂ) else
      (exponentialKernel151 (-t) b-exponentialKernel151 (-t) a)/(Complex.I*(-t:ℂ)) := by
  by_cases ht : t=0
  · simp [referenceFactor,ht,exponentialKernel151,Complex.ofReal_sub]
  · rw [if_neg ht]
    simpa only [referenceFactor, Complex.ofReal_neg] using
      integral_kernel151 (-t) a b (neg_ne_zero.mpr ht)

theorem referenceFactor_measurable (a b : ℝ) : Measurable (referenceFactor a b) := by
  have he : referenceFactor a b = fun t => if t=0 then ((b-a:ℝ):ℂ) else
      (exponentialKernel151 (-t) b-exponentialKernel151 (-t) a)/(Complex.I*(-t:ℂ)) := by
    funext t
    exact referenceFactor_formula a b t
  rw [he]
  unfold exponentialKernel151
  apply Measurable.ite (measurableSet_singleton (0 : ℝ)) measurable_const
  fun_prop

theorem referenceFactor_bound (a b t : ℝ) (ht : t ≠ 0) :
    ‖referenceFactor a b t‖ ≤ 2/|t| := by
  simpa only [referenceFactor,abs_neg] using
    norm_integral_kernel_le151 (-t) a b (neg_ne_zero.mpr ht)

theorem reference_measurable (A B : Finset ℕ) (c d : ℕ → ℝ) (a b : ℝ) :
    Measurable (mixedReference A B c d a b) :=
  ((continuous_polynomial A c).measurable.mul
    (continuous_polynomial B d).measurable).mul (referenceFactor_measurable a b)

theorem reference_bound (A B : Finset ℕ) (c d : ℕ → ℝ) (a b ell t : ℝ)
    (hl : 0 ≤ ell) (hc : (∑ n ∈ A, |c n|) ≤ ell)
    (hd : (∑ n ∈ B, |d n|) ≤ ell) (ht : t ≠ 0) :
    ‖mixedReference A B c d a b t‖ ≤ 2*ell^2/|t| := by
  have h1 := (qualitative_cap A c t).trans hc
  have h2 := (qualitative_cap B d t).trans hd
  have hh := mul_le_mul h1 h2 (norm_nonneg _) hl
  have hf := mul_le_mul hh (referenceFactor_bound a b t ht)
    (norm_nonneg _) (mul_nonneg hl hl)
  simpa only [mixedReference,norm_mul,pow_two,mul_div_assoc,
    mul_assoc,mul_left_comm,mul_comm] using hf

theorem inverse_fourth_integrable (H : ℝ) (hH : 1 ≤ H) :
    IntegrableOn (fun t : ℝ => 1/t^4) (outside H) := by
  have h := Item1CountableTail.weighted_integrable (fun t : ℝ => (1:ℂ)/(t:ℂ)) H 1 hH
    (measurable_const.div Complex.continuous_ofReal.measurable) (by
      intro t ht
      have ht1 : 1 < |t| := hH.trans_lt ht
      rw [norm_div,norm_one,Complex.norm_real,Real.norm_eq_abs]
      exact (div_le_iff₀ (by linarith : 0 < |t|)).mpr (by linarith))
  have he (t : ℝ) : ‖(1:ℂ)/(t:ℂ)‖^2/t^2 = 1/t^4 := by
    simp only [norm_div,norm_one,Complex.norm_real,Real.norm_eq_abs,div_pow,sq_abs,one_pow]
    ring
  simpa only [he] using h

theorem inverse_fourth_integral (H : ℝ) (hH : 1 ≤ H) :
    (∫ t in outside H, (1:ℝ)/t^4) = 2/(3*H^3) := by
  have hHp : 0 < H := by linarith
  have hpow (t : ℝ) : (1:ℝ)/t^4 = t^(-4:ℝ) := by
    norm_num [Real.rpow_neg_natCast,one_div]
  have hp : (∫ t in Ioi H, (1:ℝ)/t^4) = 1/(3*H^3) := by
    simp_rw [hpow]
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-4:ℝ)< -1) hHp]
    norm_num [Real.rpow_neg_natCast]
    ring
  have hn : (∫ t in Iio (-H), (1:ℝ)/t^4) = 1/(3*H^3) := by
    have hh := integral_comp_neg_Ioi H (fun t : ℝ => 1/t^4)
    have heven (t : ℝ) : (1:ℝ)/(-t)^4 = 1/t^4 := by ring
    simp only [heven,integral_Iic_eq_integral_Iio] at hh
    exact hh.symm.trans hp
  have hd : Disjoint (Iio (-H)) (Ioi H) := by
    apply Set.disjoint_left.mpr
    intro t ht hu
    change t < -H at ht
    change H < t at hu
    linarith
  have hi := inverse_fourth_integrable H hH
  have hin := hi.mono_set (by intro t ht; rw [outside_eq]; exact Or.inl ht)
  have hip' := hi.mono_set (by intro t ht; rw [outside_eq]; exact Or.inr ht)
  rw [outside_eq,setIntegral_union hd measurableSet_Ioi hin hip',hn,hp]
  ring

/-- A reference tail from its derived 1/|t| bound, not from a small-energy premise. -/
theorem reference_sharp_tail (A B : Finset ℕ) (c d : ℕ → ℝ)
    (a b ell eta H : ℝ) (hl : 0 ≤ ell) (he0 : 0 < eta) (he1 : eta ≤ 1/2)
    (hH : 1 ≤ H) (hc : (∑ n ∈ A, |c n|) ≤ ell)
    (hd : (∑ n ∈ B, |d n|) ≤ ell) :
    IntegrableOn (fun t => ‖multiplier eta t*mixedReference A B c d a b t‖^2) (outside H) ∧
    (∫ t in outside H, ‖multiplier eta t*mixedReference A B c d a b t‖^2) ≤
      32*ell^4/(3*eta^2*H^3) := by
  let F := mixedReference A B c d a b
  have hm (t : ℝ) (ht : t ∈ outside H) :
      ‖multiplier eta t*F t‖^2 ≤ (16*ell^4/eta^2)*(1/t^4) := by
    have ht0 : t ≠ 0 := by
      intro he
      have hh : H < |t| := ht
      simp only [he,abs_zero] at hh
      linarith
    have hr := pow_le_pow_left₀ (norm_nonneg (F t))
      (reference_bound A B c d a b ell t hl hc hd ht0) 2
    have hs := multiplied_square_bound F eta t he0 he1 ht0
    have hx := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (sq_nonneg t)) (show 0 ≤ 4/eta^2 by positivity)
    calc
      _ ≤ (4/eta^2)*(‖F t‖^2/t^2) := hs
      _ ≤ (4/eta^2)*((2*ell^2/|t|)^2/t^2) := hx
      _ = _ := by rw [div_pow,sq_abs]; ring
  have hmajor := (inverse_fourth_integrable H hH).const_mul (16*ell^4/eta^2)
  have hmeas := (((measurable_multiplier eta).mul
    (reference_measurable A B c d a b)).norm.pow_const 2)
  have hi : IntegrableOn (fun t => ‖multiplier eta t*F t‖^2) (outside H) := by
    apply hmajor.mono' hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (outside_measurable H)] with t ht
    change ‖(‖multiplier eta t*F t‖^2 : ℝ)‖ ≤ (16*ell^4/eta^2)*(1/t^4)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖multiplier eta t*F t‖)]
    exact hm t ht
  refine ⟨hi,?_⟩
  have hh := setIntegral_mono_on hi hmajor (outside_measurable H) hm
  rw [integral_const_mul,inverse_fourth_integral H hH] at hh
  convert hh using 1 <;> ring

/-- Complete mixed-center high-tail draft: source and reference have both been
constructed. Centering is kept; the final inequality pays both cross terms.
The first two reference coefficient lists need not be prime-supported. -/
theorem mixed_center_sharp_tail (S : Finset Triple) (w : Triple → ℝ) (N : ℕ)
    (A B : Finset ℕ) (c d : ℕ → ℝ) (a b X ell eta H : ℝ)
    (hX : 0 < X) (hl : 0 ≤ ell) (he0 : 0 < eta) (he1 : eta ≤ 1/2) (hH : 1 ≤ H)
    (hp : ∀ z ∈ S, allPrime z) (hsN : ∀ z ∈ S, 1 ≤ product z ∧ product z ≤ N)
    (hsX : ∀ z ∈ S, X/8 ≤ (product z:ℝ))
    (hw0 : ∀ z ∈ S, 0 ≤ w z) (hw : ∀ z ∈ S, w z ≤ ell^3)
    (hm : (∑ z ∈ S, w z/(product z:ℝ)) ≤ 32*ell^3)
    (hc : (∑ n ∈ A, |c n|) ≤ ell) (hd : (∑ n ∈ B, |d n|) ≤ ell) :
    (∫ t in outside H,
      ‖multiplier eta t*(literal S w t-mixedReference A B c d a b t)‖^2) ≤
      49152*ell^6/(eta^2*X*H)+98304*rowCost N*ell^6/(3*eta^2*X*H^2)+
        64*ell^4/(3*eta^2*H^3) := by
  let P := literal S w
  let R := mixedReference A B c d a b
  have hP : Measurable P := by
    have he : P = polynomial (products S) (coeff S w) := by
      funext t; exact literal_eq_collected S w t
    rw [he]
    exact (continuous_polynomial _ _).measurable
  have hPi : IntegrableOn (fun t => ‖multiplier eta t*P t‖^2) (outside H) := by
    have hi := sharp_integrable (polynomial (products S) (coeff S w)) eta H he0 he1
      (by linarith) (continuous_polynomial _ _).measurable
      (Item1FinitePolynomialTail.weighted_integrable _ _ H hH)
    simpa only [P,literal_eq_collected] using hi
  obtain ⟨hRi,hRb⟩ := reference_sharp_tail A B c d a b ell eta H hl he0 he1 hH hc hd
  have hPb := prime_sharp_tail S w N X ell eta H hX hl he0 he1 hH hp hsN hsX hw0 hw hm
  have hpoint (t : ℝ) : ‖multiplier eta t*(P t-R t)‖^2 ≤
      2*‖multiplier eta t*P t‖^2+2*‖multiplier eta t*R t‖^2 := by
    rw [mul_sub]
    have h := norm_sub_le (multiplier eta t*P t) (multiplier eta t*R t)
    have h0 := norm_nonneg (multiplier eta t*P t-multiplier eta t*R t)
    nlinarith [sq_nonneg (‖multiplier eta t*P t‖-‖multiplier eta t*R t‖)]
  have hmajor := (hPi.const_mul 2).add (hRi.const_mul 2)
  have hci : IntegrableOn (fun t => ‖multiplier eta t*(P t-R t)‖^2) (outside H) := by
    apply hmajor.mono'
      (((measurable_multiplier eta).mul (hP.sub
        (reference_measurable A B c d a b))).norm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun t => by
      change ‖(‖multiplier eta t*(P t-R t)‖^2 : ℝ)‖ ≤
        2*‖multiplier eta t*P t‖^2+2*‖multiplier eta t*R t‖^2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖multiplier eta t*(P t-R t)‖)]
      exact hpoint t)
  have h := setIntegral_mono_on hci hmajor (outside_measurable H) (fun t _ => hpoint t)
  simp only [Pi.add_apply] at h
  rw [integral_add (hPi.const_mul 2) (hRi.const_mul 2),integral_const_mul,integral_const_mul] at h
  change (∫ t in outside H, ‖multiplier eta t*(P t-R t)‖^2) ≤ _
  dsimp [P,R] at h
  apply h.trans
  calc
    _ ≤ 2*(24576*ell^6/(eta^2*X*H)+49152*rowCost N*ell^6/(3*eta^2*X*H^2))+
        2*(32*ell^4/(3*eta^2*H^3)) :=
      add_le_add (mul_le_mul_of_nonneg_left hPb (by norm_num))
        (mul_le_mul_of_nonneg_left hRb (by norm_num))
    _ = _ := by ring

end Item1CenteredPrimeTail

-- ROOT SOURCE RECURSIVE AUDIT: exact original declarations.
run_cmd do
  for target in [
    ``Item1CenteredPrimeTail.referenceFactor_formula,
    ``Item1CenteredPrimeTail.referenceFactor_measurable,
    ``Item1CenteredPrimeTail.referenceFactor_bound,
    ``Item1CenteredPrimeTail.reference_measurable,
    ``Item1CenteredPrimeTail.reference_bound,
    ``Item1CenteredPrimeTail.inverse_fourth_integrable,
    ``Item1CenteredPrimeTail.inverse_fourth_integral,
    ``Item1CenteredPrimeTail.reference_sharp_tail,
    ``Item1CenteredPrimeTail.mixed_center_sharp_tail] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1CenteredPrimeTail: 9 original theorem guards passed."
