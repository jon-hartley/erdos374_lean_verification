import TailRemainderMean

/-! Markov control of the actual harmful set by the positive first moment.
No cancellation, tail saving, or prime distribution input is assumed here. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter MeasureTheory Set
namespace TailRemainderMeasure
open TailRemainderMean PositiveSharpBoxedCount PositiveSharpRemainderRegularity

theorem harmfulSet_measure_le_positive (X s Y ε : ℝ)
    (hX : 1<X) (hY : 0<Y) (hε : 0<ε) :
    volume.real (harmfulSet X s Y ε)≤(Real.log X/(ε*Y))*
      (∫x in Icc X (2*X), max (signedRemainder X s x (x*Y/X)) 0) := by
  let c := ε*Y/Real.log X
  have hXp : 0<X := by linarith
  have hlog : 0<Real.log X := Real.log_pos hX
  have hc : 0<c := div_pos (mul_pos hε hY) hlog
  have hi := (signedRemainder_integrable X s Y).pos_part.div_const c
  have hn : 0≤ᵐ[volume.restrict (Icc X (2*X))]
      (fun x => max (signedRemainder X s x (x*Y/X)) 0/c) :=
    Filter.Eventually.of_forall (fun _ => div_nonneg (le_max_right _ _) hc.le)
  have hm := hi.measure_le_integral hn (s := harmfulSet X s Y ε) (by
    intro x hx
    have hy : 0<x*Y/X := div_pos (mul_pos (hXp.trans_le hx.2.1) hY) hXp
    have hyY := (PositiveSharpMovingWindow.window_size_bounds X Y x hXp hY.le hx.2).1
    have hr := (lt_div_iff₀ hy).mp hx.1
    have hcr : c≤signedRemainder X s x (x*Y/X) := by
      have hmul := mul_le_mul_of_nonneg_left hyY (div_pos hε hlog).le
      calc
        c = ε/Real.log X*Y := by dsimp [c]; ring
        _ ≤ ε/Real.log X*(x*Y/X) := hmul
        _ ≤ signedRemainder X s x (x*Y/X) := hr.le
    exact (le_div_iff₀ hc).mpr (by simpa using hcr.trans (le_max_left _ _)))
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
  rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hn),integral_div] at hr
  simpa [Measure.real,Measure.restrict_apply' measurableSet_Icc,harmfulSet,
    inter_assoc,c,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hr

theorem harmfulSet_measure_le_of_positiveMean (X s Y ε B : ℝ)
    (hX : 1<X) (hY : 0<Y) (hε : 0<ε)
    (hmean : positiveMean X s Y≤B) :
    volume.real (harmfulSet X s Y ε)≤X*(Real.log X/(ε*Y))*B := by
  have hXp : 0<X := by linarith
  have hh := (div_le_iff₀ hXp).mp hmean
  calc
    _ ≤ (Real.log X/(ε*Y))*
        (∫x in Icc X (2*X), max (signedRemainder X s x (x*Y/X)) 0) :=
      harmfulSet_measure_le_positive X s Y ε hX hY hε
    _ ≤ (Real.log X/(ε*Y))*(B*X) :=
      mul_le_mul_of_nonneg_left hh (div_nonneg (Real.log_pos hX).le (mul_pos hε hY).le)
    _ = _ := by ring

run_cmd do
  for decl in [``harmfulSet_measure_le_positive,``harmfulSet_measure_le_of_positiveMean] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL HARMFUL SET CONTROLLED BY POSITIVE FIRST MOMENT"
end TailRemainderMeasure
end
