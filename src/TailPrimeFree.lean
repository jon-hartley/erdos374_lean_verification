import TailRemainderMeasure
import PositiveSharpExceptionalInput

/-! The literal positive remainder first moment suffices for prime-free measure
control. Both the residual mean and this one-sided saving remain explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter MeasureTheory Set
namespace TailPrimeFree
open TailRemainderMean TailRemainderMeasure PositiveSharpExceptionalInput
open PositiveSharpResidual PositiveSharpErrorMeasure

theorem eventually_primeFree_measure_bound :
    ∃s₀:ℝ, 0<s₀ ∧ s₀≤1/1000 ∧ ∀s:ℝ, 0<s → s<s₀ →
      ∃X₀:ℝ, 2≤X₀ ∧ ∀X≥X₀, ∀Y B_E B_P:ℝ,
      0<Y → Y≤X/4 →
      (∫x in Icc X (2*X), residualAbs X x (x*Y/X))/X≤B_E →
      positiveMean X s Y≤B_P →
      volume.real (primeFree X Y)≤
        X*(2000*Real.log X)*(B_E+4096/X^((1:ℝ)/12))+
        X*(2000*Real.log X/Y)*B_P := by
  obtain ⟨s₀,hs₀,hs1,hp⟩ := PositiveSharpPrimeCriterion.eventually_prime_of_error_bounds
  obtain ⟨A,hA,he⟩ := actual_error_measure_bound
  refine ⟨s₀,hs₀,hs1,?_⟩
  intro s hs hss
  obtain ⟨B,_hB,hprime⟩ := hp s hs hss
  refine ⟨max A B,hA.trans (le_max_left _ _),?_⟩
  intro X hXX Y B_E B_P hY hYX hE hP
  have hXA : A≤X := (le_max_left _ _).trans hXX
  have hXB : B≤X := (le_max_right _ _).trans hXX
  have hX : 1<X := by linarith [hA.trans hXA]
  have hb := primeFree_measure_le X s Y (fun x hx =>
    hprime X hXB Y x hY hYX hx.1 hx.2)
  have hEbad := he X hXA Y (1/2000) B_E hY (by norm_num) hE
  have hPbad := harmfulSet_measure_le_of_positiveMean X s Y (1/2000) B_P
    hX hY (by norm_num) hP
  apply hb.trans ((add_le_add hEbad hPbad).trans_eq ?_)
  ring

theorem eventually_logarithmic_primeFree_bound :
    ∃s₀:ℝ, 0<s₀ ∧ s₀≤1/1000 ∧ ∀s:ℝ, 0<s → s<s₀ →
      ∃X₀:ℝ, 2≤X₀ ∧ ∀X≥X₀, ∀Y C_E C_P:ℝ,
      0<Y → Y≤X/4 →
      (∫x in Icc X (2*X), residualAbs X x (x*Y/X))/X≤C_E/(Real.log X)^2 →
      positiveMean X s Y≤C_P*Y/(Real.log X)^2 →
      volume.real (primeFree X Y)/X≤2000*(C_E+C_P)/Real.log X+
        8192000*Real.log X/X^((1:ℝ)/12) := by
  obtain ⟨s₀,hs₀,hs1,hp⟩ := eventually_primeFree_measure_bound
  refine ⟨s₀,hs₀,hs1,?_⟩
  intro s hs hss
  obtain ⟨X₀,hX₀,hbound⟩ := hp s hs hss
  refine ⟨X₀,hX₀,?_⟩
  intro X hXX Y C_E C_P hY hYX hE hP
  have hX : 1<X := by linarith [hX₀.trans hXX]
  have hXp : 0<X := by linarith
  have hl : 0<Real.log X := Real.log_pos hX
  have hh := div_le_div_of_nonneg_right
    (hbound X hXX Y (C_E/(Real.log X)^2) (C_P*Y/(Real.log X)^2) hY hYX hE hP) hXp.le
  apply hh.trans_eq
  field_simp
  ring

run_cmd do
  for decl in [``eventually_primeFree_measure_bound,``eventually_logarithmic_primeFree_bound] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "PRIME-FREE DENSITY BOUND FROM RESIDUAL AND POSITIVE FIRST MOMENTS"
end TailPrimeFree
end
