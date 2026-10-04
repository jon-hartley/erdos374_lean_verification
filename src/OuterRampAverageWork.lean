import OuterSmoothStepWork
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The actual piecewise-linear source transition is exactly a uniform
average of a sharp half-line. A difference of two such transitions is
therefore an averaged finite interval, the spatial object associated with
the interval-averaging Fourier kernel. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace OuterRampAverageWork
open OuterSmoothStepWork

theorem transition_average (δ x : ℝ) (hδ : 0 < δ) :
    (∫y in -δ..δ, if y ≤ x then (1:ℝ) else 0) = 2*δ*transition δ x := by
  rw [intervalIntegral.integral_of_le (by linarith)]
  change (∫y, (Iic x).indicator (1:ℝ → ℝ) y ∂volume.restrict (Ioc (-δ) δ)) = _
  rw [integral_indicator_one measurableSet_Iic,measureReal_restrict_apply measurableSet_Iic,
    inter_comm,Ioc_inter_Iic,Real.volume_real_Ioc]
  change max (min δ x - -δ) 0 = _
  by_cases hl : x ≤ -δ
  · rw [transition_zero δ x hδ hl,min_eq_right (by linarith),max_eq_right (by linarith)]
    ring
  · by_cases hu : δ ≤ x
    · rw [transition_one δ x hδ hu,min_eq_left hu,max_eq_left (by linarith)]
      ring
    · have hx : -δ < x := lt_of_not_ge hl
      have hx' : x < δ := lt_of_not_ge hu
      have hv0 : 0 ≤ (x+δ)/(2*δ) := div_nonneg (by linarith) (by positivity)
      have hv1 : (x+δ)/(2*δ) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
      rw [min_eq_right hx'.le,max_eq_left (by linarith),transition,
        min_eq_right hv1,max_eq_right hv0]
      field_simp
      ring

def compactRamp (δ M x : ℝ) : ℝ := transition δ x-transition δ (x-M)

theorem compactRamp_eq_transition (δ M x : ℝ) (hδ : 0 < δ) (hx : x ≤ M-δ) :
    compactRamp δ M x = transition δ x := by
  rw [compactRamp,transition_zero δ (x-M) hδ (by linarith),sub_zero]

theorem compactRamp_average (δ M x : ℝ) (hδ : 0 < δ) :
    (∫y in -δ..δ, ((if y ≤ x then (1:ℝ) else 0) -
      (if y ≤ x-M then (1:ℝ) else 0))) = 2*δ*compactRamp δ M x := by
  have hi (z : ℝ) : IntervalIntegrable (fun y => if y ≤ z then (1:ℝ) else 0)
      volume (-δ) δ := by
    have hc : IntegrableOn (fun _ : ℝ => (1:ℝ)) (uIoc (-δ) δ) :=
      intervalIntegrable_const.def'
    exact intervalIntegrable_iff.mpr (hc.indicator measurableSet_Iic)
  rw [intervalIntegral.integral_sub (hi x) (hi (x-M)),
    transition_average δ x hδ,transition_average δ (x-M) hδ,compactRamp,mul_sub]

theorem compactRamp_interval_average (δ M x : ℝ) (hδ : 0 < δ) (hM : 0 ≤ M) :
    (∫y in -δ..δ, if x-M < y ∧ y ≤ x then (1:ℝ) else 0) =
      2*δ*compactRamp δ M x := by
  rw [← compactRamp_average δ M x hδ]
  apply intervalIntegral.integral_congr
  intro y _
  dsimp only
  split_ifs <;> simp_all <;> linarith

run_cmd do
  for decl in [``transition_average, ``compactRamp_eq_transition,
      ``compactRamp_average, ``compactRamp_interval_average] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterRampAverageWork
