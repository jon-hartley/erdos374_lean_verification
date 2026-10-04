import SourceAngularConvolution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! v9. The globally CLIPPED reference really is an ordinary convolution.
UNCOMPILED DRAFT. Empty intersections and the two boundary points are treated
explicitly. This file never replaces the clipped profile by a global affine term.
-/
set_option autoImplicit false
set_option maxHeartbeats 18000000
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SourceProfileConvolution
open SourceWindowGeometry SourceLogWindow SourceWindowFourier SourceAngularConvolution
open ContinuousCofactorMellin MellinWindowFactor

def referenceC (ρ a b u : ℝ) : ℂ := continuousProfile ρ a b u

theorem exp_interval (a b : ℝ) :
    (∫ u in Icc a b, Real.exp u) = max 0 (Real.exp b-Real.exp a) := by
  by_cases hab : a≤b
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab, integral_exp]
    exact (max_eq_right (sub_nonneg.mpr (Real.exp_le_exp.mpr hab))).symm
  · have hba : b<a := lt_of_not_ge hab
    rw [Icc_eq_empty_of_lt hba,
      max_eq_left (sub_nonpos.mpr (Real.exp_le_exp.mpr hba.le))]
    simp

theorem exp_min (a b : ℝ) : Real.exp (min a b)=min (Real.exp a) (Real.exp b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (Real.exp_le_exp.mpr h)]
  · rw [min_eq_right h, min_eq_right (Real.exp_le_exp.mpr h)]

theorem exp_max (a b : ℝ) : Real.exp (max a b)=max (Real.exp a) (Real.exp b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (Real.exp_le_exp.mpr h)]
  · rw [max_eq_left h, max_eq_left (Real.exp_le_exp.mpr h)]

/-- Pointwise equality of the convolution and clipped elementary expression.
The integrands may differ at one interval endpoint, a null singleton. -/
theorem reference_eq_convolution (ρ a b u : ℝ) (hρ : 0<ρ) (_hρ1 : ρ<1)
    (ha : 0<a) (hab : a≤b) :
    referenceC ρ a b u = conv (kernelC ρ) (logInterval a b) u := by
  have hb : 0<b := ha.trans_le hab
  let lo := max (Real.log a) (u+Real.log ρ)
  let hi := min (Real.log b) u
  have heq : (fun v : ℝ => kernelC ρ (u-v)*logInterval a b v) =ᵐ[volume]
      (Icc lo hi).indicator (fun v : ℝ => (Real.exp (-u):ℂ)*(Real.exp v:ℂ)) := by
    filter_upwards [volume.ae_ne (u+Real.log ρ)] with v hv
    have he : ((0≤u-v ∧ u-v< -Real.log ρ) ∧
        (Real.log a≤v ∧ v≤Real.log b)) ↔ v∈Icc lo hi := by
      dsimp [lo, hi]
      simp only [mem_Icc, max_le_iff, le_min_iff]
      constructor
      · rintro ⟨⟨h0,h1⟩,⟨ha',hb'⟩⟩
        constructor <;> constructor <;> linarith
      · rintro ⟨⟨ha',hρ'⟩,⟨hb',hu'⟩⟩
        have hstrict : u+Real.log ρ<v := lt_of_le_of_ne hρ' (Ne.symm hv)
        constructor <;> constructor <;> linarith
    have hexp : (Real.exp (-(u-v)):ℂ)=(Real.exp (-u):ℂ)*(Real.exp v:ℂ) := by
      rw [show -(u-v)= -u+v by ring, Real.exp_add, Complex.ofReal_mul]
    by_cases hk : 0≤u-v ∧ u-v< -Real.log ρ <;>
      by_cases hvI : Real.log a≤v ∧ v≤Real.log b
    · have hc := he.mp ⟨hk,hvI⟩
      have hvI' : v∈Icc (Real.log a) (Real.log b) := hvI
      change (↑(if 0≤u-v ∧ u-v< -Real.log ρ then Real.exp (-(u-v)) else 0) : ℂ) *
        (Icc (Real.log a) (Real.log b)).indicator (fun _ => 1) v = _
      rw [if_pos hk, Set.indicator_of_mem hvI', mul_one, Set.indicator_of_mem hc, hexp]
    · have hc : v∉Icc lo hi := fun hc => hvI (he.mpr hc).2
      have hvI' : v∉Icc (Real.log a) (Real.log b) := hvI
      change (↑(if 0≤u-v ∧ u-v< -Real.log ρ then Real.exp (-(u-v)) else 0) : ℂ) *
        (Icc (Real.log a) (Real.log b)).indicator (fun _ => 1) v = _
      rw [Set.indicator_of_notMem hvI', mul_zero, Set.indicator_of_notMem hc]
    · have hc : v∉Icc lo hi := fun hc => hk (he.mpr hc).1
      change (↑(if 0≤u-v ∧ u-v< -Real.log ρ then Real.exp (-(u-v)) else 0) : ℂ) * _ = _
      rw [if_neg hk, Complex.ofReal_zero, zero_mul, Set.indicator_of_notMem hc]
    · have hc : v∉Icc lo hi := fun hc => hk (he.mpr hc).1
      change (↑(if 0≤u-v ∧ u-v< -Real.log ρ then Real.exp (-(u-v)) else 0) : ℂ) * _ = _
      rw [if_neg hk, Complex.ofReal_zero, zero_mul, Set.indicator_of_notMem hc]
  rw [conv_swap, integral_congr_ae heq, integral_indicator measurableSet_Icc,
    integral_const_mul, integral_complex_ofReal, exp_interval]
  dsimp [lo,hi]
  rw [exp_min, exp_max, Real.exp_log ha, Real.exp_log hb,
    Real.exp_add, Real.exp_log hρ]
  simp only [referenceC, continuousProfile, referenceLength, mul_comm (Real.exp u) ρ,
    Complex.ofReal_mul]

theorem reference_integrable (ρ a b : ℝ) (hρ : 0<ρ) (hρ1 : ρ<1)
    (ha : 0<a) (hab : a≤b) : Integrable (referenceC ρ a b) := by
  have he : referenceC ρ a b=conv (kernelC ρ) (logInterval a b) := by
    funext u
    exact reference_eq_convolution ρ a b u hρ hρ1 ha hab
  rw [he]
  exact conv_integrable _ _ (kernel_integrable ρ) (interval_integrable a b)

theorem reference_continuous (ρ a b : ℝ) : Continuous (referenceC ρ a b) := by
  unfold referenceC continuousProfile referenceLength
  fun_prop

theorem reference_transform (ρ a b t : ℝ) (hρ : 0<ρ) (hρ1 : ρ<1)
    (ha : 0<a) (hab : a≤b) :
    angular (referenceC ρ a b) t =
      MellinWindowFactor.factor 1 (1-ρ) t * cofactor a b (line 1 t) := by
  have he : referenceC ρ a b=conv (kernelC ρ) (logInterval a b) := by
    funext u
    exact reference_eq_convolution ρ a b u hρ hρ1 ha hab
  rw [he, angular_conv _ _ (kernel_integrable ρ) (interval_integrable a b),
    kernel_transform ρ t hρ hρ1, reference_interval_transform a b t ha hab]

theorem kernel_measurable (ρ : ℝ) : Measurable (kernelC ρ) := by
  rw [kernel_indicator]
  exact (by fun_prop : Measurable (fun u : ℝ => (Real.exp (-u):ℂ))).indicator measurableSet_Ico

theorem kernel_norm_le_one (ρ u : ℝ) : ‖kernelC ρ u‖≤1 := by
  by_cases hu : 0≤u ∧ u< -Real.log ρ
  · unfold kernelC kernel
    rw [if_pos hu]
    simp only [Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by linarith [hu.1])
  · simp [kernelC, kernel, hu]

theorem reference_norm_le_one (ρ a b u : ℝ) (ha : 0≤a) :
    ‖referenceC ρ a b u‖≤1 := by
  have he := Real.exp_pos u
  have hlength : 0≤referenceLength a b (ρ*Real.exp u) (Real.exp u) ∧
      referenceLength a b (ρ*Real.exp u) (Real.exp u)≤Real.exp u := by
    unfold referenceLength
    constructor
    · exact le_max_left _ _
    · apply max_le he.le
      have hl := min_le_right b (Real.exp u)
      have hr := le_max_left a (ρ*Real.exp u)
      linarith
  have hprod := mul_le_mul_of_nonneg_left hlength.2 (Real.exp_pos (-u)).le
  have hexp : Real.exp (-u)*Real.exp u=1 := by rw [←Real.exp_add]; simp
  simpa only [referenceC, Complex.norm_real, Real.norm_eq_abs,
    continuousProfile, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hlength.1), hexp] using hprod

/-- Only the two literal kernel endpoints can fail to be continuity points. -/
theorem kernel_continuousAt (ρ u : ℝ) (hu0 : u≠0) (huh : u≠ -Real.log ρ) :
    ContinuousAt (kernelC ρ) u := by
  by_cases hi : 0<u ∧ u< -Real.log ρ
  · have he : kernelC ρ =ᶠ[𝓝 u] (fun v : ℝ => (Real.exp (-v):ℂ)) := by
      filter_upwards [Ioo_mem_nhds hi.1 hi.2] with v hv
      have hv' : 0≤v ∧ v< -Real.log ρ := ⟨hv.1.le,hv.2⟩
      unfold kernelC kernel
      rw [if_pos hv']
    exact (by fun_prop : ContinuousAt (fun v : ℝ => (Real.exp (-v):ℂ)) u).congr_of_eventuallyEq he
  · have ho : u<0 ∨ -Real.log ρ<u := by
      by_cases h0 : u<0
      · exact Or.inl h0
      · have hp : 0<u := lt_of_le_of_ne (le_of_not_gt h0) (Ne.symm hu0)
        have hnot : ¬ u< -Real.log ρ := fun h => hi ⟨hp,h⟩
        exact Or.inr (lt_of_le_of_ne (le_of_not_gt hnot) (Ne.symm huh))
    have he : kernelC ρ =ᶠ[𝓝 u] (fun _ : ℝ => (0:ℂ)) := by
      rcases ho with ho | ho
      · filter_upwards [Iio_mem_nhds ho] with v hv
        change v < 0 at hv
        have hv' : ¬ (0≤v ∧ v< -Real.log ρ) := fun h => (not_le_of_gt hv) h.1
        simp [kernelC, kernel, hv']
      · filter_upwards [Ioi_mem_nhds ho] with v hv
        change -Real.log ρ < v at hv
        have hv' : ¬ (0≤v ∧ v< -Real.log ρ) := fun h => (not_lt_of_ge hv.le) h.2
        simp [kernelC, kernel, hv']
    exact continuousAt_const.congr_of_eventuallyEq he

#print axioms reference_transform
run_cmd do
  for n in [``exp_interval, ``exp_min, ``exp_max, ``reference_eq_convolution,
      ``reference_integrable, ``reference_continuous, ``reference_transform,
      ``kernel_measurable, ``kernel_norm_le_one, ``reference_norm_le_one,
      ``kernel_continuousAt] do
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "V9 CLIPPED CONVOLUTION: VALID ONLY AFTER ACTUAL COMPILATION"
end SourceProfileConvolution
