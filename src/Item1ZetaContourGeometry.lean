import Item1PositiveStripDefinitions
import Item1RampLineDefinitions
import Item1EntireRampKernel
import Item1RightLineBound
import Item1ShiftedCapRectangle
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
UNCOMPILED. Actual shifted-zeta integrand and its rectangle. The only new
analytic premise is PositiveStrip, stated about the genuine zeta logarithmic
derivative. NO proof of this stronger strip is supplied. Its (3/4,9) exponents
must not be replaced by the inherited, insufficient (9,9) theorem.
-/
set_option autoImplicit false
set_option maxHeartbeats 18000000
noncomputable section
open MeasureTheory Set Filter
namespace Item1ZetaContourGeometry
open Item1LogRampSmoothing Item1EntireRampKernel Item1RampMellinInversion
open Item1RampDirichlet Item1RightLineBound Item1ShiftedCapRectangle

def heightLog (t : ℝ) : ℝ := Real.log (2*t)
def depth (a t : ℝ) : ℝ := a/(heightLog t)^(3/4:ℝ)
def integrand (N δ t : ℝ) (z : ℂ) : ℂ :=
  zetaLogDeriv (1+(t:ℂ)*Complex.I+z)*
    Complex.exp (z*(Real.log N:ℂ))*kernel (Real.log 2) δ z

def rect (c d T : ℝ) : Set ℂ :=
  {z | -d ≤ z.re ∧ z.re ≤ c ∧ -T ≤ z.im ∧ z.im ≤ T}

theorem heightLog_pos (t : ℝ) (ht : 8 ≤ t) : 0 < heightLog t := by
  unfold heightLog
  exact Real.log_pos (by linarith)

theorem heightLog_ge_one (t : ℝ) (ht : 8 ≤ t) : 1 ≤ heightLog t := by
  have he : Real.exp 1 ≤ 2*t := by
    have hh := Real.exp_one_lt_d9
    linarith
  simpa [heightLog] using Real.log_le_log (Real.exp_pos 1) he

theorem depth_bounds (a t : ℝ) (ha : 0 < a) (ha1 : a ≤ 1/2) (ht : 8 ≤ t) :
    0 < depth a t ∧ depth a t ≤ 1/2 := by
  have hp := heightLog_pos t ht
  have hpow : 1 ≤ (heightLog t)^(3/4:ℝ) :=
    Real.one_le_rpow (heightLog_ge_one t ht) (by norm_num)
  constructor
  · exact div_pos ha (Real.rpow_pos_of_pos hp _)
  · unfold depth
    exact (div_le_self ha.le hpow).trans ha1

/-- Uniform height/real-part data for every point of the actual finite rectangle. -/
theorem strip_point (a C T₀ t c σ v : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1/2) (hT : 4 ≤ T₀)
    (ht : 8 ≤ t) (htT : 2*T₀ ≤ t) (hc : c ≤ 1)
    (hσ : σ ∈ Icc (-depth a t) c) (hv : v ∈ Icc (-t/2) (t/2))
    (hs : PositiveStrip a C T₀) :
    DifferentiableAt ℂ zetaLogDeriv (1+(t:ℂ)*Complex.I+line σ v) ∧
      ‖zetaLogDeriv (1+(t:ℂ)*Complex.I+line σ v)‖ ≤ C*(heightLog t)^9 := by
  have hy : T₀ ≤ t+v := by linarith [hv.1]
  have hyp : 1 < t+v := by linarith
  have hyhi : t+v ≤ 2*t := by linarith [hv.2]
  have hlp : 0 < Real.log (t+v) := Real.log_pos hyp
  have hl : Real.log (t+v) ≤ heightLog t :=
    Real.log_le_log (by linarith) hyhi
  have hp : (Real.log (t+v))^(3/4:ℝ) ≤ (heightLog t)^(3/4:ℝ) :=
    Real.rpow_le_rpow hlp.le hl (by norm_num)
  have hd : depth a t ≤ a/(Real.log (t+v))^(3/4:ℝ) := by
    exact div_le_div_of_nonneg_left ha.le (Real.rpow_pos_of_pos hlp _) hp
  have hlo : 1-a/(Real.log (t+v))^(3/4:ℝ) ≤ 1+σ := by linarith [hσ.1]
  have hh := hs (1+σ) (t+v) hy hlo (by linarith [hσ.2])
  have he : 1+(t:ℂ)*Complex.I+line σ v = ((1+σ:ℝ):ℂ)+((t+v:ℝ):ℂ)*Complex.I := by
    unfold line
    push_cast
    ring
  rw [he]
  refine ⟨hh.1, hh.2.trans ?_⟩
  have hC : 0 ≤ C := by
    have hlog : 0 < (Real.log (t+v))^9 := pow_pos hlp 9
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hh.2) hlog
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlp.le hl 9) hC

/-- The actual integrand is differentiable on the Cauchy rectangle. -/
theorem integrand_differentiableAt (N δ a C T₀ t c : ℝ)
    (hδ : 0 ≤ δ) (ha : 0 < a) (ha1 : a ≤ 1/2)
    (hT : 4 ≤ T₀) (ht : 8 ≤ t) (htT : 2*T₀ ≤ t) (hc : c ≤ 1)
    (hs : PositiveStrip a C T₀) (z : ℂ) (hz : z ∈ rect c (depth a t) (t/2)) :
    DifferentiableAt ℂ (integrand N δ t) z := by
  have he : line z.re z.im = z := by simp [line]
  have hp := (strip_point a C T₀ t c z.re z.im ha ha1 hT ht htT hc
    ⟨hz.1,hz.2.1⟩ ⟨by simpa only [neg_div] using hz.2.2.1,hz.2.2.2⟩ hs).1
  rw [he] at hp
  have hshift : DifferentiableAt ℂ (fun w : ℂ => 1+(t:ℂ)*Complex.I+w) z := by fun_prop
  have hf := hp.comp z hshift
  have hexp : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (w*(Real.log N:ℂ))) z := by fun_prop
  exact (hf.mul hexp).mul
    (kernel_differentiable (Real.log 2) δ (Real.log_nonneg (by norm_num)) hδ z)

theorem integrand_rectangle (N δ a C T₀ t c : ℝ)
    (hδ : 0 ≤ δ) (ha : 0 < a) (ha1 : a ≤ 1/2) (hT : 4 ≤ T₀)
    (ht : 8 ≤ t) (htT : 2*T₀ ≤ t) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hs : PositiveStrip a C T₀) :
    DifferentiableOn ℂ (integrand N δ t)
      (uIcc (-depth a t) c ×ℂ uIcc (-t/2) (t/2)) := by
  have hd := depth_bounds a t ha ha1 ht
  intro z hz
  have hz' : z ∈ rect c (depth a t) (t/2) := by
    simpa [rect,Complex.mem_reProdIm,and_assoc,neg_div,
      uIcc_of_le (show -depth a t ≤ c by linarith),
      uIcc_of_le (show -(t/2) ≤ t/2 by linarith)] using hz
  exact (integrand_differentiableAt N δ a C T₀ t c hδ ha ha1 hT ht htT hc1 hs z hz').differentiableWithinAt

theorem exp_norm (N σ v : ℝ) :
    ‖Complex.exp (line σ v*(Real.log N:ℂ))‖ = Real.exp (σ*Real.log N) := by
  simp [Complex.norm_exp,line]

/-- Actual translated-zeta bound on the left side, with its exponential saving. -/
theorem left_pointwise (N δ a C T₀ t c v : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1/2) (hC : 0 ≤ C) (hT : 4 ≤ T₀)
    (ht : 8 ≤ t) (htT : 2*T₀ ≤ t) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hv : v ∈ Icc (-t/2) (t/2)) (hs : PositiveStrip a C T₀) :
    ‖integrand N δ t (line (-depth a t) v)‖ ≤
      C*(heightLog t)^9*Real.exp (-depth a t*Real.log N)*
        ‖kernel (Real.log 2) δ (line (-depth a t) v)‖ := by
  have hd := depth_bounds a t ha ha1 ht
  have hb := (strip_point a C T₀ t c (-depth a t) v ha ha1 hT ht htT hc1
    ⟨le_rfl,by linarith⟩ hv hs).2
  simp only [integrand,norm_mul,exp_norm]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le) (norm_nonneg _)

/-- A real-part bound for the two horizontal edges; all multiplicative losses retained. -/
theorem horizontal_pointwise (N δ a C T₀ t c σ v : ℝ)
    (hN : 1 ≤ N) (hδ : 0 < δ) («hδλ» : δ ≤ Real.log 2)
    (ha : 0 < a) (ha1 : a ≤ 1/2) (hC : 0 ≤ C) (hT : 4 ≤ T₀)
    (ht : 8 ≤ t) (htT : 2*T₀ ≤ t) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hσ : σ ∈ Icc (-depth a t) c) (hv : v = t/2 ∨ v = -t/2)
    (hs : PositiveStrip a C T₀) :
    ‖integrand N δ t (line σ v)‖ ≤
      9*Real.exp (c*Real.log N)*C*(heightLog t)^9/(δ*(t/2)^2) := by
  have hR : 0 ≤ heightLog t := (heightLog_pos t ht).le
  have hvI : v ∈ Icc (-t/2) (t/2) := by rcases hv with rfl|rfl <;> constructor <;> linarith
  have hv2 : v^2 = (t/2)^2 := by rcases hv with rfl|rfl <;> ring
  have hv0 : v ≠ 0 := by intro he; rw [he] at hv2; nlinarith
  have hz0 : line σ v ≠ 0 := by intro he; have := congrArg Complex.im he; simp [line] at this; contradiction
  have hzn : (t/2)^2 ≤ ‖line σ v‖^2 := by
    have heq : ‖line σ v‖^2 = σ^2+v^2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply,line,pow_two]
    rw [heq,hv2]
    nlinarith [sq_nonneg σ]
  have hz := (strip_point a C T₀ t c σ v ha ha1 hT ht htT hc1 hσ hvI hs).2
  have hk := kernel_norm_decay (Real.log 2) δ hδ «hδλ»
    (by rw [Real.exp_log (by norm_num)]) (line σ v) (by simpa [line] using hσ.2.trans hc1) hz0
  have hk' : ‖kernel (Real.log 2) δ (line σ v)‖ ≤ 9/(δ*(t/2)^2) :=
    hk.trans (div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left hzn hδ.le))
  have he : Real.exp (σ*Real.log N) ≤ Real.exp (c*Real.log N) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hσ.2 (Real.log_nonneg hN))
  simp only [integrand,norm_mul,exp_norm]
  have hh := mul_le_mul (mul_le_mul hz he (Real.exp_pos _).le (by positivity)) hk'
    (norm_nonneg _) (by positivity)
  convert hh using 1 <;> ring

/-- Quantitative right line, valid even when the translated imaginary part is zero. -/
theorem right_pointwise (N δ t c v : ℝ) (hδ : 0 < δ) («hδλ» : δ ≤ Real.log 2)
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hv : v ≠ 0) :
    ‖integrand N δ t (line c v)‖ ≤
      54*Real.exp (c*Real.log N)/(c^2*δ*v^2) := by
  have hz0 : line c v ≠ 0 := by intro he; have := congrArg Complex.re he; simp [line] at this; linarith
  have he : 1+(t:ℂ)*Complex.I+line c v = 1+(c:ℂ)+((t+v:ℝ):ℂ)*Complex.I := by
    unfold line; push_cast; ring
  have hz := zetaLogDeriv_right_bound c (t+v) hc0 hc1
  rw [←he] at hz
  have hk := kernel_norm_decay (Real.log 2) δ hδ «hδλ»
    (by rw [Real.exp_log (by norm_num)]) (line c v) (by simpa [line] using hc1) hz0
  have hzn : v^2 ≤ ‖line c v‖^2 := by
    have heq : ‖line c v‖^2 = c^2+v^2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply,line,pow_two]
    rw [heq]
    nlinarith [sq_nonneg c]
  have hk' := hk.trans (div_le_div_of_nonneg_left (by norm_num)
    (mul_pos hδ (sq_pos_of_ne_zero hv)) (mul_le_mul_of_nonneg_left hzn hδ.le))
  simp only [integrand,norm_mul,exp_norm]
  have hh := mul_le_mul_of_nonneg_right hz (Real.exp_pos (c*Real.log N)).le
  have hh' := mul_le_mul hh hk' (norm_nonneg _) (by positivity)
  convert hh' using 1 <;> ring

end Item1ZetaContourGeometry

run_cmd do
  for target in [
    ``Item1ZetaContourGeometry.heightLog_pos,
    ``Item1ZetaContourGeometry.heightLog_ge_one,
    ``Item1ZetaContourGeometry.depth_bounds,
    ``Item1ZetaContourGeometry.strip_point,
    ``Item1ZetaContourGeometry.integrand_differentiableAt,
    ``Item1ZetaContourGeometry.integrand_rectangle,
    ``Item1ZetaContourGeometry.exp_norm,
    ``Item1ZetaContourGeometry.left_pointwise,
    ``Item1ZetaContourGeometry.horizontal_pointwise,
    ``Item1ZetaContourGeometry.right_pointwise] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Item1ZetaContourGeometry.right_pointwise

