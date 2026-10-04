import Item1ZetaContourGeometry
import Item1RampDirichlet
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Group.Integral

/-!
UNCOMPILED. Numerical bounds for the ACTUAL zeta contour integrals.
Both infinite tails of the right line are paid. No evenness of the shifted
zeta integrand is asserted: reflection is used only for the real majorant v^-2.
The genuine stronger zeta premise PositiveStrip remains visible.
-/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
open MeasureTheory Set Filter
namespace Item1ContourIntegralBounds
open Item1LogRampSmoothing Item1EntireRampKernel Item1RampMellinInversion
open Item1RampDirichlet Item1RightLineBound Item1ShiftedCapRectangle
open Item1ZetaContourGeometry

/-- This complement is exactly both open infinite tails, including no zero. -/
def tails (T : ℝ) : Set ℝ := (Icc (-T) T)ᶜ

theorem tails_eq (T : ℝ) : tails T = Iio (-T) ∪ Ioi T := by
  ext v
  simp only [tails,mem_compl_iff,mem_Icc,mem_union,mem_Iio,mem_Ioi]
  constructor
  · intro h
    by_cases hv : v < -T
    · exact Or.inl hv
    · exact Or.inr (lt_of_not_ge (fun hb => h ⟨le_of_not_gt hv,hb⟩))
  · rintro (h|h) hh <;> linarith [hh.1,hh.2]

/-- Elementary complete majorant integral; no finite-frequency truncation. -/
theorem inverse_square_tails (T : ℝ) (hT : 0 < T) :
    IntegrableOn (fun v : ℝ => 1/v^2) (tails T) ∧
      (∫ v in tails T, (1:ℝ)/v^2) = 2/T := by
  let f : ℝ → ℝ := fun v => 1/v^2
  have hpw : f = fun v => v^(-2:ℝ) := by
    funext v
    norm_num [f,Real.rpow_neg_natCast,div_eq_mul_inv]
  have hip : IntegrableOn f (Ioi T) := by
    rw [hpw]
    exact integrableOn_Ioi_rpow_of_lt (by norm_num) hT
  have hp : (∫ v in Ioi T, f v) = 1/T := by
    rw [hpw,integral_Ioi_rpow_of_lt (by norm_num) hT]
    norm_num [Real.rpow_neg_natCast,Real.rpow_neg_one,div_eq_mul_inv]
  have even : ∀ v, f (-v) = f v := by intro v; simp [f]
  have hneg : Integrable ((Ioi T).indicator f ∘ Neg.neg) :=
    (hip.integrable_indicator measurableSet_Ioi).comp_neg
  have hid : (Ioi T).indicator f ∘ Neg.neg = (Iio (-T)).indicator f := by
    funext v
    by_cases hv : v < -T
    · have hn : T < -v := by linarith
      simp [Function.comp_apply,hv,hn,even]
    · have hn : ¬ T < -v := by linarith
      simp [Function.comp_apply,hv,hn]
  rw [hid] at hneg
  have hin : IntegrableOn f (Iio (-T)) :=
    (integrable_indicator_iff measurableSet_Iio).mp hneg
  have hn : (∫ v in Iio (-T), f v) = 1/T := by
    have hh := integral_comp_neg_Ioi T f
    simp only [even,integral_Iic_eq_integral_Iio] at hh
    exact hh.symm.trans hp
  have hd : Disjoint (Iio (-T)) (Ioi T) := by
    apply disjoint_left.mpr
    intro v hv hv'
    change v < -T at hv
    change T < v at hv'
    linarith
  constructor
  · rw [tails_eq]
    exact hin.union hip
  · change (∫ v in tails T, f v) = _
    rw [tails_eq,setIntegral_union hd measurableSet_Ioi hin hip,hn,hp]
    ring

/-- All finite path integrals are genuinely integrable before estimating them. -/
theorem vertical_integrable (N δ a C T₀ t c σ : ℝ)
    (hδ : 0 ≤ δ) (ha : 0 < a) (ha1 : a ≤ 1/2) (hT : 4 ≤ T₀)
    (ht : 8 ≤ t) (htT : 2*T₀ ≤ t) (hc1 : c ≤ 1)
    (hσ : σ ∈ Icc (-depth a t) c) (hs : PositiveStrip a C T₀) :
    IntegrableOn (fun v => integrand N δ t (line σ v)) (Icc (-t/2) (t/2)) := by
  have hcont : ContinuousOn (fun v => integrand N δ t (line σ v))
      (Icc (-t/2) (t/2)) := by
    intro v hv
    have hz : line σ v ∈ rect c (depth a t) (t/2) := by
      simpa [rect,line,neg_div] using And.intro hσ.1 (And.intro hσ.2 hv)
    have hd := integrand_differentiableAt N δ a C T₀ t c hδ ha ha1 hT ht htT hc1 hs _ hz
    have hl : ContinuousAt (fun u : ℝ => line σ u) v := by
      dsimp only [line]
      fun_prop
    exact (hd.continuousAt.comp hl).continuousWithinAt
  exact hcont.integrableOn_Icc

theorem horizontal_integrable (N δ a C T₀ t c v : ℝ)
    (hδ : 0 ≤ δ) (ha : 0 < a) (ha1 : a ≤ 1/2) (hT : 4 ≤ T₀)
    (ht : 8 ≤ t) (htT : 2*T₀ ≤ t) (hc1 : c ≤ 1)
    (hv : v ∈ Icc (-t/2) (t/2)) (hs : PositiveStrip a C T₀) :
    IntegrableOn (fun σ => integrand N δ t (line σ v)) (Icc (-depth a t) c) := by
  have hcont : ContinuousOn (fun σ => integrand N δ t (line σ v))
      (Icc (-depth a t) c) := by
    intro σ hσ
    have hz : line σ v ∈ rect c (depth a t) (t/2) := by
      simpa [rect,line,neg_div] using And.intro hσ.1 (And.intro hσ.2 hv)
    have hd := integrand_differentiableAt N δ a C T₀ t c hδ ha ha1 hT ht htT hc1 hs _ hz
    have hl : ContinuousAt (fun u : ℝ => line u v) σ := by
      dsimp only [line]
      fun_prop
    exact (hd.continuousAt.comp (f := fun u : ℝ => line u v) (x := σ) hl).continuousWithinAt
  exact hcont.integrableOn_Icc

/-- The exponential saving is retained in the actual left vertical integral. -/
theorem left_vertical_bound (N δ a C T₀ t c : ℝ)
    (hδ : 0 < δ) («hδλ» : δ ≤ Real.log 2) (ha : 0 < a) (ha1 : a ≤ 1/2)
    (hC : 0 ≤ C) (hT : 4 ≤ T₀) (ht : 8 ≤ t) (htT : 2*T₀ ≤ t)
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hs : PositiveStrip a C T₀) :
    ‖vertical (integrand N δ t) (-depth a t) (t/2)‖ ≤
      18*Real.pi*C*(heightLog t)^9*Real.exp (-depth a t*Real.log N)/δ := by
  have hR : 0 ≤ heightLog t := (heightLog_pos t ht).le
  let k : ℝ → ℂ := fun v => kernel (Real.log 2) δ (line (-depth a t) v)
  let Q := C*(heightLog t)^9*Real.exp (-depth a t*Real.log N)
  have hd := depth_bounds a t ha ha1 ht
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have «hλ» : Real.log (2:ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have «hλe» : Real.exp (Real.log (2:ℝ)) ≤ 2 := by rw [Real.exp_log (by norm_num)]
  have hk : Integrable k := kernel_vertical_integrable (Real.log 2) δ (-depth a t)
    hδ «hδλ» «hλ» «hλe» (by linarith)
  have hj := vertical_integrable N δ a C T₀ t c (-depth a t)
    hδ.le ha ha1 hT ht htT hc1 ⟨le_rfl,by linarith⟩ hs
  have hb : ∀ v ∈ Icc (-t/2) (t/2),
      ‖integrand N δ t (line (-depth a t) v)‖ ≤ Q*‖k v‖ := by
    intro v hv
    exact left_pointwise N δ a C T₀ t c v ha ha1 hC hT ht htT hc0 hc1 hv hs
  have hi := setIntegral_mono_on hj.norm (hk.norm.integrableOn.const_mul Q)
    measurableSet_Icc hb
  rw [integral_const_mul] at hi
  have hsub := setIntegral_le_integral (s:=Icc (-t/2) (t/2)) hk.norm
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
  have hmass := kernel_vertical_norm_integral (Real.log 2) δ (-depth a t)
    hδ «hδλ» «hλ» «hλe» (by linarith)
  have hn : ‖vertical (integrand N δ t) (-depth a t) (t/2)‖ ≤
      ∫ v in Icc (-t/2) (t/2), ‖integrand N δ t (line (-depth a t) v)‖ := by
    simp only [vertical,norm_mul,Complex.norm_I,one_mul]
    rw [intervalIntegral.integral_of_le (show -(t/2) ≤ t/2 by linarith),
      ←integral_Icc_eq_integral_Ioc]
    simp only [neg_div]
    exact norm_integral_le_integral_norm _
  apply (hn.trans hi).trans
  have hh := mul_le_mul_of_nonneg_left (hsub.trans hmass) hQ
  convert hh using 1 <;> dsimp [Q,k] <;> ring

/-- Each of the two horizontal edges, not their sum. -/
theorem horizontal_bound (N δ a C T₀ t c v : ℝ)
    (hN : 1 ≤ N) (hδ : 0 < δ) («hδλ» : δ ≤ Real.log 2)
    (ha : 0 < a) (ha1 : a ≤ 1/2) (hC : 0 ≤ C) (hT : 4 ≤ T₀)
    (ht : 8 ≤ t) (htT : 2*T₀ ≤ t) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hv : v = t/2 ∨ v = -t/2) (hs : PositiveStrip a C T₀) :
    ‖horizontal (integrand N δ t) (-depth a t) c v‖ ≤
      18*Real.exp (c*Real.log N)*C*(heightLog t)^9/(δ*(t/2)^2) := by
  have hR : 0 ≤ heightLog t := (heightLog_pos t ht).le
  have hd := depth_bounds a t ha ha1 ht
  have hab : -depth a t ≤ c := by linarith
  have hvI : v ∈ Icc (-t/2) (t/2) := by rcases hv with rfl|rfl <;> constructor <;> linarith
  have _hi := horizontal_integrable N δ a C T₀ t c v
    hδ.le ha ha1 hT ht htT hc1 hvI hs
  let Q := 9*Real.exp (c*Real.log N)*C*(heightLog t)^9/(δ*(t/2)^2)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=-depth a t) (b:=c) (C:=Q) (f:=fun σ => integrand N δ t (line σ v)) (by
      intro σ hσ
      have hσ' : σ ∈ Icc (-depth a t) c := by
        rw [uIoc_of_le hab] at hσ
        exact ⟨hσ.1.le,hσ.2⟩
      exact horizontal_pointwise N δ a C T₀ t c σ v
        hN hδ «hδλ» ha ha1 hC hT ht htT hc0 hc1 hσ' hv hs)
  have hlen : |c-(-depth a t)| ≤ 2 := by rw [abs_of_nonneg (by linarith)]; linarith
  apply hn.trans
  have hh := mul_le_mul_of_nonneg_left hlen hQ
  convert hh using 1 <;> dsimp [Q] <;> ring

/-- Both complete infinite tails of the original right line. No strip is needed. -/
theorem right_tail_bound (N δ t c T : ℝ) (hδ : 0 < δ) («hδλ» : δ ≤ Real.log 2)
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hT : 0 < T) :
    (∫ v in tails T, ‖integrand N δ t (line c v)‖) ≤
      108*Real.exp (c*Real.log N)/(c^2*δ*T) := by
  have hi : Integrable (fun v => integrand N δ t (line c v)) :=
    zeta_right_integrand_integrable N δ t c hδ «hδλ» hc0 hc1
  have ht := inverse_square_tails T hT
  let Q := 54*Real.exp (c*Real.log N)/(c^2*δ)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hb : ∀ v ∈ tails T, ‖integrand N δ t (line c v)‖ ≤ Q*(1/v^2) := by
    intro v hv
    have hv0 : v ≠ 0 := by
      intro he
      subst v
      exact hv ⟨by linarith,by linarith⟩
    convert right_pointwise N δ t c v hδ «hδλ» hc0 hc1 hv0 using 1 <;> dsimp [Q] <;> ring
  have hm := setIntegral_mono_on hi.norm.integrableOn (ht.1.const_mul Q)
    measurableSet_Icc.compl hb
  rw [integral_const_mul,ht.2] at hm
  convert hm using 1 <;> dsimp [Q] <;> ring

end Item1ContourIntegralBounds

run_cmd do
  for target in [
    ``Item1ContourIntegralBounds.tails_eq,
    ``Item1ContourIntegralBounds.inverse_square_tails,
    ``Item1ContourIntegralBounds.vertical_integrable,
    ``Item1ContourIntegralBounds.horizontal_integrable,
    ``Item1ContourIntegralBounds.left_vertical_bound,
    ``Item1ContourIntegralBounds.horizontal_bound,
    ``Item1ContourIntegralBounds.right_tail_bound] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Item1ContourIntegralBounds.right_tail_bound

