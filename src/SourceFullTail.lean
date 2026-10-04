import SourceDyadicTail
import SourceProductBlock
import SourceCenteredMiddle
import RealFrequencyReflection

/-!
v8. The whole two-sided source spectral tail, not just its dyadic blocks.
UNCOMPILED DRAFT. All source coefficients and supports remain literal.
The amplitude cap proves integrability independently of the sharp block saving.
The only inherited estimates are the earlier draft block and reference lemmas;
no prime-polynomial cancellation or low-frequency PNT is used here.
-/
set_option autoImplicit false
set_option maxHeartbeats 18000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators ComplexConjugate
namespace SourceFullTail
open SourceDyadicTail SourceProductBlock SourceLiteralMiddle
open SourceLiteralMoments SourceLiteralMass SourceReferenceSigmaOne SourceCenteredMiddle
open PositiveInteriorModel PositiveInteriorCells

 theorem product_continuous (X : ℝ) (j : ℕ×ℕ) : Continuous (sourceProduct X j) :=
  ((factor_continuous X j 0).mul (factor_continuous X j 1)).mul (factor_continuous X j 2)

 theorem product_cap (X : ℝ) (j : ℕ×ℕ) (hX : 2≤X)
    (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X)) (t : ℝ) :
    ‖sourceProduct X j t‖≤3375 := by
  have h0 := factor_norm_le_fifteen X j 0 t hX hlog hj
  have h1 := factor_norm_le_fifteen X j 1 t hX hlog hj
  have h2 := factor_norm_le_fifteen X j 2 t hX hlog hj
  have h01 := mul_le_mul h0 h1 (norm_nonneg _) (by norm_num)
  have h012 := mul_le_mul h01 h2 (norm_nonneg _) (by norm_num)
  norm_num at h012
  simpa only [sourceProduct,norm_mul] using h012

 theorem product_norm_even (X t : ℝ) (j : ℕ×ℕ) :
    ‖sourceProduct X j (-t)‖=‖sourceProduct X j t‖ := by
  have hi (i : Fin 3) : factor X j i (-t)=conj (factor X j i t) := by
    exact RealFrequencyReflection.vertical_real (support X j i)
      ArithmeticFunction.vonMangoldt 1 t
  simp only [sourceProduct,hi,←map_mul,Complex.norm_conj]

 theorem product_tail_integrable (X U : ℝ) (j : ℕ×ℕ) (hX : 2≤X)
    (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X)) (hU : 1≤U) :
    IntegrableOn (fun t => ‖sourceProduct X j t‖^2/t^2) (outside U) :=
  weighted_integrable (sourceProduct X j) U 3375 hU
    (product_continuous X j).measurable (fun t _ => product_cap X j hX hlog hj t)

/-- All dyadic intervals are included; no upper bound on their frequencies is imposed. -/
 theorem product_positive_tail (X U : ℝ) (j : ℕ×ℕ) (hX : 2≤X)
    (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X)) (hU : 1≤U) :
    (∫ t in Ioi U, ‖sourceProduct X j t‖^2/t^2) ≤
      blockConstant*(1+Real.log X)^4*(2/(X*U)+4/(3*U^2)) := by
  have hUp : 0<U := by linarith
  have hi := product_tail_integrable X U j hX hlog hj hU
  have hip : IntegrableOn (fun t => ‖sourceProduct X j t‖^2/t^2) (Ici U) := by
    apply (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
    exact hi.mono_set (by
      intro t ht
      change U< |t|
      rw [abs_of_pos (hUp.trans ht)]
      exact ht)
  have hb := integral_le_of_blocks (fun t => ‖sourceProduct X j t‖^2/t^2) U
    (blockConstant*(1+Real.log X)^4/X) (blockConstant*(1+Real.log X)^4) hUp hip (by
      intro k
      have ht := weighted_source_block X (SourceDyadicTail.scale U k) j
        hX hlog hj (SourceDyadicTail.scale_pos U hUp k)
      rw [integral_Icc_eq_integral_Ico] at ht
      change (∫ t in Ico (SourceDyadicTail.scale U k) (SourceDyadicTail.scale U (k+1)),
        ‖sourceProduct X j t‖^2/t^2)≤_
      rw [scale_succ]
      convert ht using 1 <;> ring)
  convert hb using 1 <;> ring

 theorem product_tail (X U : ℝ) (j : ℕ×ℕ) (hX : 2≤X)
    (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X)) (hU : 1≤U) :
    (∫ t in outside U, ‖sourceProduct X j t‖^2/t^2) ≤
      blockConstant*(1+Real.log X)^4*(4/(X*U)+8/(3*U^2)) := by
  have hh := symmetric_of_even (fun t => ‖sourceProduct X j t‖^2/t^2) U
    (blockConstant*(1+Real.log X)^4*(2/(X*U)+4/(3*U^2))) (by linarith)
    (product_tail_integrable X U j hX hlog hj hU)
    (fun t => by rw [product_norm_even,neg_sq])
    (product_positive_tail X U j hX hlog hj hU)
  convert hh using 1 <;> ring

/-- The reference tail has its own integrability proof, not a borrowed source cap. -/
 theorem reference_tail_integrable (X U : ℝ) (j : ℕ×ℕ) (hX : 2≤X)
    (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X)) (hU : 1≤U) :
    IntegrableOn (fun t => ‖referenceProduct X j t‖^2/t^2) (outside U) := by
  apply weighted_integrable (referenceProduct X j) U 450 hU
    (reference_continuous X j (by linarith)).measurable
  intro t ht
  have habs : 1< |t| := hU.trans_lt ht
  have ht0 : t≠0 := by intro he; norm_num [he] at habs
  exact (reference_norm X t j hX hlog hj ht0).trans
    ((div_le_iff₀ (by linarith : 0< |t|)).mpr (by linarith))

 theorem inverse_fourth_tail (U : ℝ) (hU : 0<U) :
    (∫ t in outside U, (202500:ℝ)/t^4)=135000/U^3 := by
  let f : ℝ→ℝ := fun t => (202500:ℝ)/t^4
  have hpower : f=fun t => 202500*t^(-4:ℝ) := by
    funext t
    norm_num [f,Real.rpow_neg_natCast,div_eq_mul_inv]
  have hip : IntegrableOn f (Ioi U) := by
    rw [hpower]
    exact (integrableOn_Ioi_rpow_of_lt (by norm_num : (-4:ℝ) < -1) hU).const_mul 202500
  have hp : (∫ t in Ioi U, f t)=67500/U^3 := by
    rw [hpower,integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num) hU]
    norm_num [Real.rpow_neg_natCast]
    ring
  have heven : ∀ t, f (-t)=f t := by intro t; dsimp [f]; ring
  -- Qualitative integrability on the other half-line follows by negation of
  -- the integrable positive-tail indicator, not from its totalized integral.
  have hneg : Integrable ((Ioi U).indicator f ∘ Neg.neg) :=
    (hip.integrable_indicator measurableSet_Ioi).comp_neg
  have hid : (Ioi U).indicator f ∘ Neg.neg=(Iio (-U)).indicator f := by
    funext t
    by_cases ht : t< -U
    · have hn : U< -t := by linarith
      simp [Function.comp_apply,ht,hn,heven]
    · have hn : ¬U< -t := by linarith
      simp [Function.comp_apply,ht,hn]
  rw [hid] at hneg
  have hin : IntegrableOn f (Iio (-U)) :=
    (integrable_indicator_iff measurableSet_Iio).mp hneg
  have hn : (∫ t in Iio (-U), f t)=67500/U^3 := by
    have hh := integral_comp_neg_Ioi U f
    simp only [heven,integral_Iic_eq_integral_Iio] at hh
    exact hh.symm.trans hp
  have hd : Disjoint (Iio (-U)) (Ioi U) := by
    apply Set.disjoint_left.mpr
    intro t ht hu
    change t < -U at ht
    change U < t at hu
    linarith
  rw [outside_eq,setIntegral_union hd measurableSet_Ioi hin hip,hn,hp]
  ring

 theorem reference_tail (X U : ℝ) (j : ℕ×ℕ) (hX : 2≤X)
    (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X)) (hU : 1≤U) :
    (∫ t in outside U, ‖referenceProduct X j t‖^2/t^2)≤135000/U^3 := by
  have hUp : 0<U := by linarith
  have hmajor : IntegrableOn (fun t : ℝ => (202500:ℝ)/t^4) (outside U) := by
    have hh := weighted_integrable (fun t : ℝ => (450:ℂ)/(t:ℂ)) U 450 hU
      (measurable_const.div Complex.continuous_ofReal.measurable) (by
        intro t ht
        rw [norm_div,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs]
        apply (div_le_iff₀ (hUp.trans ht)).mpr
        linarith [hU.trans_lt ht])
    have he (t : ℝ) : ‖(450:ℂ)/(t:ℂ)‖^2/t^2=(202500:ℝ)/t^4 := by
      simp only [norm_div,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,div_pow,sq_abs]
      norm_num
      ring
    simpa only [he] using hh
  have hm := setIntegral_mono_on
    (reference_tail_integrable X U j hX hlog hj hU) hmajor (outside_measurable U) (by
      intro t ht
      have ht0 : t≠0 := by intro he; simp [outside,he] at ht; linarith
      have hh := pow_le_pow_left₀ (norm_nonneg _) (reference_norm X t j hX hlog hj ht0) 2
      have hd := div_le_div_of_nonneg_right hh (sq_nonneg t)
      have he : (450/|t|)^2/t^2=(202500:ℝ)/t^4 := by rw [div_pow,sq_abs]; norm_num; ring
      simpa only [he] using hd)
  exact hm.trans_eq (inverse_fourth_tail U hUp)

 theorem centered_tail_integrable (X U : ℝ) (j : ℕ×ℕ) (hX : 2≤X)
    (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X)) (hU : 1≤U) :
    IntegrableOn (fun t => ‖centeredProduct X j t‖^2/t^2) (outside U) := by
  apply weighted_integrable (centeredProduct X j) U (3375+450) hU
    (centered_continuous X j (by linarith)).measurable
  intro t ht
  have ht1 : 1< |t| := hU.trans_lt ht
  have ht0 : t≠0 := by intro he; norm_num [he] at ht1
  have hr := (reference_norm X t j hX hlog hj ht0).trans
    ((div_le_iff₀ (by linarith : 0< |t|)).mpr (by linarith : (450:ℝ)≤450*|t|))
  exact (norm_sub_le _ _).trans (add_le_add (product_cap X j hX hlog hj t) hr)

/-- No low or middle-frequency analytic assumption is needed for the whole tail. -/
 theorem centered_tail (X U : ℝ) (j : ℕ×ℕ) (hX : 2≤X)
    (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X)) (hU : 1≤U) :
    (∫ t in outside U, ‖centeredProduct X j t‖^2/t^2) ≤
      blockConstant*(1+Real.log X)^4*(8/(X*U)+16/(3*U^2))+270000/U^3 := by
  have hF := product_tail_integrable X U j hX hlog hj hU
  have hR := reference_tail_integrable X U j hX hlog hj hU
  have hm := setIntegral_mono_on (centered_tail_integrable X U j hX hlog hj hU)
    ((hF.const_mul 2).add (hR.const_mul 2)) (outside_measurable U) (by
      intro t _
      have hh := norm_sub_le (sourceProduct X j t) (referenceProduct X j t)
      have hn := norm_nonneg (sourceProduct X j t-referenceProduct X j t)
      have hs : ‖centeredProduct X j t‖^2≤
          2*‖sourceProduct X j t‖^2+2*‖referenceProduct X j t‖^2 := by
        change ‖sourceProduct X j t-referenceProduct X j t‖^2≤_
        nlinarith [sq_nonneg (‖sourceProduct X j t‖-‖referenceProduct X j t‖)]
      simp only [Pi.add_apply]
      convert div_le_div_of_nonneg_right hs (sq_nonneg t) using 1 <;> ring)
  simp only [Pi.add_apply] at hm
  rw [integral_add (hF.const_mul 2) (hR.const_mul 2),integral_const_mul,integral_const_mul] at hm
  have hp := product_tail X U j hX hlog hj hU
  have hr := reference_tail X U j hX hlog hj hU
  apply hm.trans
  calc
    _ ≤ 2*(blockConstant*(1+Real.log X)^4*(4/(X*U)+8/(3*U^2)))+
        2*(135000/U^3) :=
      add_le_add (mul_le_mul_of_nonneg_left hp (by norm_num))
        (mul_le_mul_of_nonneg_left hr (by norm_num))
    _ = _ := by ring

 theorem normalized_tail (X Y U : ℝ) (j : ℕ×ℕ) (hX : 2≤X)
    (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X)) (hU : 1≤U) (hY : 0<Y) :
    (X/Y)^2*(∫ t in outside U, ‖centeredProduct X j t‖^2/t^2) ≤
      8*blockConstant*(1+Real.log X)^4*X/(Y^2*U)+
      (16/3)*blockConstant*(1+Real.log X)^4*X^2/(Y^2*U^2)+
      270000*X^2/(Y^2*U^3) := by
  have hh := mul_le_mul_of_nonneg_left (centered_tail X U j hX hlog hj hU) (sq_nonneg (X/Y))
  have hXp : 0<X := by linarith
  have hUp : 0<U := by linarith
  convert hh using 1 <;> field_simp <;> ring

#print axioms centered_tail
run_cmd do
  for n in [``product_continuous,``product_cap,``product_norm_even,
      ``product_tail_integrable,``product_positive_tail,``product_tail,
      ``reference_tail_integrable,``inverse_fourth_tail,``reference_tail,
      ``centered_tail_integrable,``centered_tail,``normalized_tail] do
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "V8 FULL SOURCE TAIL: VALID ONLY AFTER SUCCESSFUL COMPILATION"
end SourceFullTail
