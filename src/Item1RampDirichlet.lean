import Item1RampSumDefinitions
import Item1ZetaDirichletSeries
import Item1PositiveStripDefinitions
import Item1RampMellinInversion
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
Absolute termwise inversion and the actual Mangoldt specialization.
The final smoothed identity has no zero-free-strip, cap, inversion, or Fubini premise.
This is an identity on a right line, NOT a prime cancellation estimate.
-/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators FourierTransform
namespace Item1RampDirichlet
open Item1LogRampSmoothing Item1EntireRampKernel Item1RampFourier
open Item1RampMellinInversion

/-- Qualitative absolute summability suffices for the interchange. -/
theorem termwise_inversion (a : ℕ → ℂ) (u : ℕ → ℝ) («λ» δ c : ℝ)
    (hδ : 0 < δ) («hδλ» : δ ≤ «λ») («hλ1» : «λ» ≤ 1)
    («hλexp» : Real.exp «λ» ≤ 2) (hc : c ≤ 1)
    (hsum : Summable (fun n => ‖a n‖*Real.exp (-c*u n))) :
    (∑' n : ℕ, a n*(weight «λ» δ (u n):ℂ)) =
      ((1/(2*Real.pi):ℝ):ℂ) *
        (∫ v : ℝ, (∑' n : ℕ, a n*Complex.exp (-line c v*(u n:ℂ)))*
          kernel «λ» δ (line c v)) := by
  let F : ℕ → ℝ → ℂ := fun n v => a n*inverseIntegrand «λ» δ c (u n) v
  have hi (n : ℕ) : Integrable (F n) :=
    (inverse_integrable «λ» δ c (u n) hδ «hδλ» «hλ1» «hλexp» hc).const_mul _
  have hn (n : ℕ) : (∫ v : ℝ, ‖F n v‖) =
      (‖a n‖*Real.exp (-c*u n))*(∫ v : ℝ, ‖kernel «λ» δ (line c v)‖) := by
    simp only [F,norm_mul]
    rw [integral_const_mul,inverse_norm_integral «λ» δ c (u n) hδ «hδλ» «hλ1» «hλexp» hc]
    ring
  have hnSum : Summable (fun n => ∫ v : ℝ, ‖F n v‖) := by
    simp_rw [hn]
    exact hsum.mul_right _
  have swap := integral_tsum_of_summable_integral_norm hi hnSum
  have hpoint (v : ℝ) : (∑' n, F n v) =
      (∑' n, a n*Complex.exp (-line c v*(u n:ℂ)))*kernel «λ» δ (line c v) := by
    simp only [F,inverseIntegrand,←mul_assoc]
    exact tsum_mul_right
  have hterm (n : ℕ) : a n*(weight «λ» δ (u n):ℂ) =
      ((1/(2*Real.pi):ℝ):ℂ)*(∫ v : ℝ, F n v) := by
    rw [weight_inversion «λ» δ c (u n) hδ «hδλ» «hλ1» «hλexp» hc]
    simp only [F,integral_const_mul]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left,swap]
  simp_rw [hpoint]

/-- A pointwise right-line majorant gives genuine integrability, not a totalized integral. -/
theorem series_integrand_integrable (a : ℕ → ℂ) (u : ℕ → ℝ) («λ» δ c : ℝ)
    (hδ : 0 < δ) («hδλ» : δ ≤ «λ») («hλ1» : «λ» ≤ 1)
    («hλexp» : Real.exp «λ» ≤ 2) (hc : c ≤ 1)
    (hsum : Summable (fun n => ‖a n‖*Real.exp (-c*u n))) :
    Integrable (fun v : ℝ =>
      (∑' n, a n*Complex.exp (-line c v*(u n:ℂ)))*kernel «λ» δ (line c v)) := by
  let b : ℕ → ℝ := fun n => ‖a n‖*Real.exp (-c*u n)
  let P : ℕ → ℝ → ℂ := fun n v => a n*Complex.exp (-line c v*(u n:ℂ))
  have hp (n : ℕ) (v : ℝ) : ‖P n v‖ = b n := by
    simp [P,b,line,Complex.norm_exp]
  have hPc : Continuous (fun v : ℝ => ∑' n, P n v) :=
    continuous_tsum (fun n => by dsimp [P,line]; fun_prop) hsum
      (fun n v => (hp n v).le)
  have hnorm (v : ℝ) : Summable (fun n => ‖P n v‖) := by
    simp_rw [hp]
    exact hsum
  have hcap (v : ℝ) : ‖∑' n, P n v‖ ≤ ∑' n, b n := by
    have hh := norm_tsum_le_tsum_norm (hnorm v)
    simpa only [hp] using hh
  have hKi := kernel_vertical_integrable «λ» δ c hδ «hδλ» «hλ1» «hλexp» hc
  have hline : Continuous (line c) := by
    change Continuous (fun v : ℝ => (c:ℂ) + (v:ℂ)*Complex.I)
    fun_prop
  have hcont : Continuous (fun v : ℝ => (∑' n, P n v)*kernel «λ» δ (line c v)) :=
    hPc.mul ((kernel_continuous «λ» δ (by linarith) hδ.le).comp hline)
  apply (hKi.norm.const_mul (∑' n, b n)).mono' hcont.aestronglyMeasurable
  filter_upwards with v
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hcap v) (norm_nonneg _)

theorem damped_coefficient_identity (N c t : ℝ) (n : ℕ) :
    ‖coefficient t n‖*Real.exp (-c*position N n) =
      Real.exp (c*Real.log N)*
        ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m:ℂ))
          ((1:ℂ)+(c:ℂ)) (n+1)‖ := by
  rw [lseries_term_exp]
  simp only [coefficient,position,norm_mul,Complex.norm_exp]
  simp only [Complex.mul_re,Complex.neg_re,Complex.add_re,Complex.ofReal_re,
    Complex.ofReal_im,Complex.one_re,Complex.I_re,Complex.I_im,
    mul_zero,sub_zero,mul_one]
  rw [mul_assoc,←Real.exp_add]
  rw [mul_comm (Real.exp (c*Real.log N)),mul_assoc,←Real.exp_add]
  congr 2
  ring

theorem mangoldt_absolute_sum (N c t : ℝ) (hc : 0 < c) :
    Summable (fun n => ‖coefficient t n‖*Real.exp (-c*position N n)) := by
  have hz : 1 < (((1:ℂ)+(c:ℂ)):ℂ).re := by simpa using hc
  have hi : Summable (LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m:ℂ))
      ((1:ℂ)+(c:ℂ))) := ArithmeticFunction.LSeriesSummable_vonMangoldt hz
  have hn : Summable (fun n =>
      ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m:ℂ))
        ((1:ℂ)+(c:ℂ)) n‖) := summable_norm_iff.mpr hi
  simp_rw [damped_coefficient_identity]
  exact ((summable_nat_add_iff 1).2 hn).mul_left _

theorem translated_series (N c t v : ℝ) (hc : 0 < c) :
    (∑' n, coefficient t n*Complex.exp (-line c v*(position N n:ℂ))) =
      Complex.exp (line c v*(Real.log N:ℂ))*
        zetaLogDeriv (1+(t:ℂ)*Complex.I+line c v) := by
  have hterm (n : ℕ) :
      coefficient t n*Complex.exp (-line c v*(position N n:ℂ)) =
      Complex.exp (line c v*(Real.log N:ℂ))*
        ((ArithmeticFunction.vonMangoldt (n+1):ℂ)*
          Complex.exp (-(1+(t:ℂ)*Complex.I+line c v)*(Real.log (n+1:ℕ):ℂ))) := by
    unfold coefficient position
    rw [mul_assoc,←Complex.exp_add]
    rw [mul_comm (Complex.exp (line c v*(Real.log N:ℂ))),mul_assoc,←Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [hterm]
  rw [tsum_mul_left,logarithmic_derivative_series]
  simpa [line] using hc

theorem smoothSeries_eq_finite (N δ t : ℝ) (hN : 0 < N)
    (hδ : 0 < δ) («hδλ» : δ ≤ Real.log 2) :
    smoothSeries N δ t = smoothFinite N δ t := by
  unfold smoothSeries smoothFinite
  apply tsum_eq_sum
  intro n hn
  have hlarge : Nat.ceil (4*N) ≤ n := by simpa [Finset.mem_range,not_lt] using hn
  have hnc : (Nat.ceil (4*N):ℝ) ≤ n := by exact_mod_cast hlarge
  have hp : 4*N ≤ (n+1:ℕ) := by
    have hh := Nat.le_ceil (4*N)
    have hcast : ((n+1:ℕ):ℝ) = (n:ℝ)+1 := by norm_num
    rw [hcast]
    linarith
  have hl := Real.log_le_log (show 0<4*N by positivity) hp
  have hlog4 : Real.log (4:ℝ) = 2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  rw [Real.log_mul (by norm_num : (4:ℝ)≠0) hN.ne',hlog4] at hl
  have hw := weight_right (Real.log 2) δ (position N n)
    (Real.log_nonneg (by norm_num)) hδ (by unfold position; linarith)
  simp [hw]

/-- Actual finite Mangoldt smoothing equals the absolutely convergent zeta integral.
No zero-free strip, polynomial cap, or contour-shift identity is assumed. -/
theorem smoothed_zeta_identity (N δ t c : ℝ) (hN : 0 < N)
    (hδ : 0 < δ) («hδλ» : δ ≤ Real.log 2) (hc : 0 < c) (hc1 : c ≤ 1) :
    smoothFinite N δ t = ((1/(2*Real.pi):ℝ):ℂ)*
      (∫ v : ℝ, zetaLogDeriv (1+(t:ℂ)*Complex.I+line c v)*
        Complex.exp (line c v*(Real.log N:ℂ))*
          kernel (Real.log 2) δ (line c v)) := by
  have «hλ1» : Real.log (2:ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh ⊢
    exact hh
  have «hλexp» : Real.exp (Real.log (2:ℝ)) ≤ 2 := by rw [Real.exp_log (by norm_num)]
  rw [←smoothSeries_eq_finite N δ t hN hδ «hδλ»]
  have hh := termwise_inversion (coefficient t) (position N) (Real.log 2) δ c
    hδ «hδλ» «hλ1» «hλexp» hc1 (mangoldt_absolute_sum N c t hc)
  unfold smoothSeries
  rw [hh]
  congr 1
  apply integral_congr_ae
  filter_upwards with v
  rw [translated_series N c t v hc]
  ring

theorem zeta_right_integrand_integrable (N δ t c : ℝ)
    (hδ : 0 < δ) («hδλ» : δ ≤ Real.log 2) (hc : 0 < c) (hc1 : c ≤ 1) :
    Integrable (fun v : ℝ => zetaLogDeriv (1+(t:ℂ)*Complex.I+line c v)*
      Complex.exp (line c v*(Real.log N:ℂ))*kernel (Real.log 2) δ (line c v)) := by
  have «hλ1» : Real.log (2:ℝ) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have «hλexp» : Real.exp (Real.log (2:ℝ)) ≤ 2 := by rw [Real.exp_log (by norm_num)]
  have hh := series_integrand_integrable (coefficient t) (position N) (Real.log 2) δ c
    hδ «hδλ» «hλ1» «hλexp» hc1 (mangoldt_absolute_sum N c t hc)
  convert hh using 1
  funext v
  rw [translated_series N c t v hc]
  ring

end Item1RampDirichlet

-- ROOT CAP RECURSIVE AUDIT: original declarations only.
run_cmd do
  for target in [
    ``Item1RampDirichlet.termwise_inversion,
    ``Item1RampDirichlet.series_integrand_integrable,
    ``Item1RampDirichlet.cpow_positive_exp,
    ``Item1RampDirichlet.lseries_term_exp,
    ``Item1RampDirichlet.logarithmic_derivative_series,
    ``Item1RampDirichlet.damped_coefficient_identity,
    ``Item1RampDirichlet.mangoldt_absolute_sum,
    ``Item1RampDirichlet.translated_series,
    ``Item1RampDirichlet.smoothSeries_eq_finite,
    ``Item1RampDirichlet.smoothed_zeta_identity,
    ``Item1RampDirichlet.zeta_right_integrand_integrable] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1RampDirichlet: 11 original theorem guards passed."
