import Item1EntireRampKernel
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Tactic

/-!
Actual logarithmic ramp weight = convolution of two boxes.
The source's arithmetic reference is not changed by this auxiliary construction.
-/
set_option autoImplicit false
set_option maxHeartbeats 18000000
noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform BigOperators
namespace Item1RampFourier
open Item1LogRampSmoothing Item1EntireRampKernel

def overlap («λ» δ u : ℝ) : ℝ := max 0 (min «λ» u-max 0 (u-δ))
def box (a c : ℝ) : ℝ → ℂ :=
  (Icc (0:ℝ) a).indicator (fun u => Complex.exp ((c:ℂ)*(u:ℂ)))
def tilted («λ» δ c u : ℝ) : ℂ :=
  Complex.exp ((c:ℂ)*(u:ℂ))*(weight «λ» δ u:ℂ)
def conv (f g : ℝ → ℂ) : ℝ → ℂ :=
  MeasureTheory.convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume

theorem ramp_middle (δ u : ℝ) (hδ : 0 < δ) (hu : 0 ≤ u) (huδ : u ≤ δ) :
    ramp δ u = u/δ := by
  have h0 : 0 ≤ u/δ := div_nonneg hu hδ.le
  have h1 : u/δ ≤ 1 := (div_le_one hδ).mpr huδ
  simp [ramp,max_eq_right h0,min_eq_right h1]

theorem overlap_eq_weight («λ» δ u : ℝ) (hδ : 0 < δ) («hδλ» : δ ≤ «λ») :
    overlap «λ» δ u = δ*weight «λ» δ u := by
  have «hλ» : 0 ≤ «λ» := by linarith
  rcases le_or_gt u 0 with hu | hu
  · rw [weight_left «λ» δ u «hλ» hδ hu]
    simp [overlap,min_eq_right (by linarith : u ≤ «λ»),
      max_eq_left (by linarith : u-δ ≤ 0),max_eq_left hu]
  rcases le_or_gt u δ with huδ | huδ
  · rw [weight,ramp_middle δ u hδ hu.le huδ,
      ramp_zero δ (u-«λ») hδ (by linarith)]
    simp [overlap,min_eq_right (by linarith : u ≤ «λ»),
      max_eq_left (by linarith : u-δ ≤ 0),max_eq_right hu.le]
    field_simp
  rcases le_or_gt u «λ» with «huλ» | «huλ»
  · rw [weight_core «λ» δ u hδ huδ.le «huλ»]
    simp [overlap,min_eq_right «huλ»,max_eq_right (by linarith : 0 ≤ u-δ),
      max_eq_right hδ.le]
  rcases le_or_gt u («λ»+δ) with humax | humax
  · rw [weight,ramp_one δ u hδ huδ.le,
      ramp_middle δ (u-«λ») hδ (by linarith) (by linarith)]
    simp only [overlap,min_eq_left «huλ».le,max_eq_right (by linarith : 0 ≤ u-δ)]
    rw [max_eq_right (by linarith : 0 ≤ «λ»-(u-δ))]
    field_simp
    ring
  · rw [weight_right «λ» δ u «hλ» hδ humax.le]
    simp [overlap,min_eq_left «huλ».le,max_eq_right (by linarith : 0 ≤ u-δ),
      max_eq_left (by linarith : «λ»-(u-δ) ≤ 0)]

theorem box_integrable (a c : ℝ) : Integrable (box a c) := by
  have hi : IntegrableOn (fun u : ℝ => Complex.exp ((c:ℂ)*(u:ℂ))) (Icc (0:ℝ) a) :=
    (by fun_prop : Continuous (fun u : ℝ => Complex.exp ((c:ℂ)*(u:ℂ)))).integrableOn_Icc
  exact hi.integrable_indicator measurableSet_Icc

theorem box_product («λ» δ c u v : ℝ) :
    box «λ» c v * box δ c (u-v) =
      (Icc (max 0 (u-δ)) (min «λ» u)).indicator
        (fun _ => Complex.exp ((c:ℂ)*(u:ℂ))) v := by
  have hm : (v ∈ Icc (0:ℝ) «λ» ∧ u-v ∈ Icc (0:ℝ) δ) ↔
      v ∈ Icc (max 0 (u-δ)) (min «λ» u) := by
    simp only [mem_Icc,max_le_iff,le_min_iff]
    constructor <;> rintro ⟨⟨ha,hb⟩,⟨hc,hd⟩⟩ <;> constructor <;> constructor <;> linarith
  by_cases ha : v ∈ Icc (0:ℝ) «λ»
  · by_cases hb : u-v ∈ Icc (0:ℝ) δ
    · have hh : v ∈ Icc (max 0 (u-δ)) (min «λ» u) := hm.mp ⟨ha,hb⟩
      simp only [box,indicator_of_mem ha,indicator_of_mem hb,indicator_of_mem hh]
      rw [←Complex.exp_add]
      congr 1
      push_cast
      ring
    · have hn : v ∉ Icc (max 0 (u-δ)) (min «λ» u) := fun h => hb (hm.mpr h).2
      simp [box,ha,hb,hn]
  · have hn : v ∉ Icc (max 0 (u-δ)) (min «λ» u) := fun h => ha (hm.mpr h).1
    simp [box,ha,hn]

theorem box_convolution («λ» δ c u : ℝ) :
    conv (box «λ» c) (box δ c) u =
      (overlap «λ» δ u:ℂ)*Complex.exp ((c:ℂ)*(u:ℂ)) := by
  unfold conv
  rw [MeasureTheory.convolution_mul]
  simp_rw [box_product]
  rw [integral_indicator measurableSet_Icc]
  simp [integral_const,Real.volume_Icc,Measure.real,overlap,
    ENNReal.toReal_ofReal',mul_comm,max_comm]

theorem tilted_eq_convolution («λ» δ c : ℝ) (hδ : 0 < δ) («hδλ» : δ ≤ «λ») :
    tilted «λ» δ c = fun u => (conv (box «λ» c) (box δ c) u)/(δ:ℂ) := by
  funext u
  rw [box_convolution,overlap_eq_weight «λ» δ u hδ «hδλ»]
  unfold tilted
  push_cast
  have hδc : (δ:ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  field_simp [hδc]

theorem tilted_continuous («λ» δ c : ℝ) : Continuous (tilted «λ» δ c) := by
  unfold tilted weight ramp
  fun_prop

theorem tilted_integrable («λ» δ c : ℝ) (hδ : 0 < δ) («hδλ» : δ ≤ «λ») :
    Integrable (tilted «λ» δ c) := by
  rw [tilted_eq_convolution «λ» δ c hδ «hδλ»]
  exact (MeasureTheory.Integrable.integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) (box_integrable «λ» c) (box_integrable δ c)).div_const _

theorem fourier_box (a c ξ : ℝ) (ha : 0 ≤ a) :
    𝓕 (box a c) ξ = primitive a ((c:ℂ)-(2*Real.pi*ξ:ℝ)*Complex.I) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  have he : (fun u : ℝ => Complex.exp ((-2*Real.pi*u*ξ:ℝ)*Complex.I) * box a c u) =
      (Icc (0:ℝ) a).indicator
        (fun u => Complex.exp (((c:ℂ)-(2*Real.pi*ξ:ℝ)*Complex.I)*(u:ℂ))) := by
    funext u
    by_cases hu : u ∈ Icc (0:ℝ) a
    · simp only [box,indicator_of_mem hu]
      rw [←Complex.exp_add]
      congr 1
      push_cast
      ring
    · simp [box,hu]
  rw [he,integral_indicator measurableSet_Icc,←primitive_set a ha]

theorem fourier_tilted («λ» δ c ξ : ℝ) (hδ : 0 < δ) («hδλ» : δ ≤ «λ») :
    𝓕 (tilted «λ» δ c) ξ = kernel «λ» δ ((c:ℂ)-(2*Real.pi*ξ:ℝ)*Complex.I) := by
  rw [tilted_eq_convolution «λ» δ c hδ «hδλ»]
  have hdiv (f : ℝ → ℂ) : 𝓕 (fun u => f u/(δ:ℂ)) ξ = (𝓕 f ξ)/(δ:ℂ) := by
    rw [Real.fourier_eq',Real.fourier_eq']
    simp only [smul_eq_mul,←mul_div_assoc,integral_div]
  rw [hdiv]
  have hc := Real.fourier_mul_convolution_eq (box_integrable «λ» c) (box_integrable δ c) ξ
  change 𝓕 (conv (box «λ» c) (box δ c)) ξ = _ at hc
  rw [hc,fourier_box «λ» c ξ (by linarith),fourier_box δ c ξ hδ.le]
  rfl

end Item1RampFourier

run_cmd do
  for target in [``Item1RampFourier.ramp_middle, ``Item1RampFourier.overlap_eq_weight,
    ``Item1RampFourier.box_integrable, ``Item1RampFourier.box_product,
    ``Item1RampFourier.box_convolution, ``Item1RampFourier.tilted_eq_convolution,
    ``Item1RampFourier.tilted_continuous, ``Item1RampFourier.tilted_integrable,
    ``Item1RampFourier.fourier_box, ``Item1RampFourier.fourier_tilted] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Item1RampFourier.box_convolution
#print axioms Item1RampFourier.fourier_tilted
