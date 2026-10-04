import SourceLogWindow
import SourceReferenceSigmaOne
import MellinWindowFactor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Group.Integral

/-!
v8. Exact ANGULAR-frequency transforms of the sharp log-window and the
continuous-reference log interval. UNCOMPILED DRAFT.
These are the two building-block transforms needed by the source Fourier
assembly. No Parseval identity, source raw mean, or external prime estimate
is postulated here. The convention exp(-i t u) is explicit; it is NOT silently
identified with Mathlib's exp(-2 pi i xi u) convention.
-/
set_option autoImplicit false
set_option maxHeartbeats 14000000
noncomputable section
open MeasureTheory Set
namespace SourceWindowFourier
open SourceLogWindow SourceReferenceSigmaOne ContinuousCofactorMellin MellinWindowFactor

def angular (f : ℝ→ℂ) (t : ℝ) : ℂ :=
  ∫ u : ℝ, Complex.exp (-Complex.I*(t:ℂ)*(u:ℂ))*f u

def kernelC (ρ u : ℝ) : ℂ := SourceLogWindow.kernel ρ u

def logInterval (a b : ℝ) : ℝ→ℂ := (Icc (Real.log a) (Real.log b)).indicator (fun _ => 1)

 theorem kernel_indicator (ρ : ℝ) :
    kernelC ρ=(Ico 0 (-Real.log ρ)).indicator (fun u : ℝ => (Real.exp (-u):ℂ)) := by
  funext u
  by_cases hu : 0≤u ∧ u< -Real.log ρ
  · simp [kernelC,SourceLogWindow.kernel,Set.mem_Ico,hu]
  · simp [kernelC,SourceLogWindow.kernel,Set.mem_Ico,hu]

 theorem kernel_integrable (ρ : ℝ) : Integrable (kernelC ρ) := by
  rw [kernel_indicator]
  have hc : Continuous (fun u : ℝ => (Real.exp (-u):ℂ)) := by fun_prop
  have hi : IntegrableOn (fun u : ℝ => (Real.exp (-u):ℂ)) (Ico 0 (-Real.log ρ)) :=
    hc.integrableOn_Icc.mono_set Ico_subset_Icc_self
  exact hi.integrable_indicator measurableSet_Ico

 theorem interval_integrable (a b : ℝ) : Integrable (logInterval a b) := by
  unfold logInterval
  exact (continuous_const.integrableOn_Icc : IntegrableOn (fun _ : ℝ => (1:ℂ))
    (Icc (Real.log a) (Real.log b)) volume).integrable_indicator measurableSet_Icc

 theorem phase_norm (t u : ℝ) : ‖Complex.exp (-Complex.I*(t:ℂ)*(u:ℂ))‖=1 := by
  rw [Complex.norm_exp]
  simp

 theorem angular_integrand_integrable (f : ℝ→ℂ) (t : ℝ) (hf : Integrable f) :
    Integrable (fun u : ℝ => Complex.exp (-Complex.I*(t:ℂ)*(u:ℂ))*f u) := by
  have hc : Continuous (fun u : ℝ => Complex.exp (-Complex.I*(t:ℂ)*(u:ℂ))) := by fun_prop
  apply hf.bdd_mul (c:=1) hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun u => (phase_norm t u).le)

/-- All real frequencies, including zero. The denominator has real part one. -/
 theorem kernel_transform (ρ t : ℝ) (hρ : 0<ρ) (hρ1 : ρ<1) :
    angular (kernelC ρ) t=MellinWindowFactor.factor 1 (1-ρ) t := by
  have hh : 0< -Real.log ρ := neg_pos.mpr (Real.log_neg hρ hρ1)
  have hsn : -line 1 t≠0 := neg_ne_zero.mpr (line_ne_zero 1 t (by norm_num))
  have hint : (fun u : ℝ => Complex.exp (-Complex.I*(t:ℂ)*(u:ℂ))*kernelC ρ u)=
      (Ico 0 (-Real.log ρ)).indicator
        (fun u : ℝ => Complex.exp ((-line 1 t)*(u:ℂ))) := by
    funext u
    rw [kernel_indicator]
    by_cases hu : u∈Ico 0 (-Real.log ρ)
    · rw [Set.indicator_of_mem hu,Set.indicator_of_mem hu,Complex.ofReal_exp,←Complex.exp_add]
      congr 1
      simp only [line,Complex.ofReal_one,Complex.ofReal_neg]
      ring
    · simp only [Set.indicator_of_notMem hu,mul_zero]
  unfold angular
  rw [hint,integral_indicator measurableSet_Ico,integral_Ico_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le hh.le,integral_exp_mul_complex hsn]
  have hend : Complex.exp ((-line 1 t)*((-Real.log ρ:ℝ):ℂ))=(ρ:ℂ)^(line 1 t) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hρ.ne'),
      ←Complex.ofReal_log hρ.le]
    congr 1
    push_cast
    ring
  rw [hend]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,MellinWindowFactor.factor,
    sub_sub_cancel]
  ring

/-- The Fourier transform of the unweighted log interval is exactly the
continuous Mellin cofactor, with the t=0 value treated by its integral. -/
 theorem reference_interval_transform (a b t : ℝ) (ha : 0<a) (hab : a≤b) :
    angular (logInterval a b) t=cofactor a b (line 1 t) := by
  have hb : 0<b := ha.trans_le hab
  have hlab : Real.log a≤Real.log b := Real.log_le_log ha hab
  have hint : (fun u : ℝ => Complex.exp (-Complex.I*(t:ℂ)*(u:ℂ))*logInterval a b u)=
      (Icc (Real.log a) (Real.log b)).indicator
        (fun u : ℝ => Complex.exp ((-Complex.I*(t:ℂ))*(u:ℂ))) := by
    funext u
    by_cases hu : u∈Icc (Real.log a) (Real.log b)
    · simp [logInterval,hu,mul_assoc]
    · simp [logInterval,hu]
  unfold angular
  rw [hint,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le hlab]
  by_cases ht : t=0
  · subst t
    simp only [Complex.ofReal_zero,mul_zero,neg_zero,zero_mul,Complex.exp_zero,
      intervalIntegral.integral_const]
    have hco : cofactor a b (line 1 0)=(Real.log (b/a):ℂ) := by
      unfold cofactor
      have he : (fun u : ℝ => (u:ℂ)^(-line 1 0))=fun u => ((u⁻¹:ℝ):ℂ) := by
        funext u
        simp [line,Complex.cpow_neg_one]
      rw [he,integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hab,
        intervalIntegral.integral_ofReal,integral_inv_of_pos ha hb]
    rw [hco,Real.log_div hb.ne' ha.ne']
    simp
  · have htn : (-Complex.I*(t:ℂ))≠0 :=
      mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr ht)
    rw [integral_exp_mul_complex htn,SourceReferenceSigmaOne.quotient a b t ha hab ht]
    have hline : (1:ℂ)-line 1 t= -Complex.I*(t:ℂ) := by
      simp only [line, Complex.ofReal_one]
      ring
    rw [hline]
    have endpoint (z : ℝ) (hz : 0<z) :
        Complex.exp ((-Complex.I*(t:ℂ))*(Real.log z:ℂ))=(z:ℂ)^(-Complex.I*(t:ℂ)) := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hz.ne'),
        ←Complex.ofReal_log hz.le]
      congr 1
      ring
    rw [endpoint b hb,endpoint a ha]

/-- Translation in angular convention. There is no unrecorded factor 2 pi. -/
 theorem translate (f : ℝ→ℂ) (v t : ℝ) :
    angular (fun u => f (u-v)) t=
      Complex.exp (-Complex.I*(t:ℂ)*(v:ℂ))*angular f t := by
  have hh := integral_sub_right_eq_self (μ := volume)
    (fun u : ℝ => Complex.exp (-Complex.I*(t:ℂ)*((u+v:ℝ):ℂ))*f u) v
  have he : (fun u : ℝ => Complex.exp (-Complex.I*(t:ℂ)*((u+v:ℝ):ℂ))*f u)=
      (fun u : ℝ => Complex.exp (-Complex.I*(t:ℂ)*(v:ℂ))*
        (Complex.exp (-Complex.I*(t:ℂ)*(u:ℂ))*f u)) := by
    funext u
    rw [←mul_assoc,←Complex.exp_add]
    congr 2
    push_cast
    ring
  simp only [sub_add_cancel] at hh
  rw [he,integral_const_mul] at hh
  exact hh

#print axioms kernel_transform
run_cmd do
  for n in [``kernel_indicator,``kernel_integrable,``interval_integrable,``phase_norm,
      ``angular_integrand_integrable,``kernel_transform,``reference_interval_transform,
      ``translate] do
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "V8 ANGULAR BUILDING BLOCKS: PARSEVAL AND FULL SOURCE TRANSFORM NOT ASSERTED"
end SourceWindowFourier
