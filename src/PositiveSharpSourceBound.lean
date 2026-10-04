import PositiveSharpBuchstab
import PositiveSharpResidual
import SieveSignedBoxedModelPositive

/-! Actual positive Buchstab count against the explicit model and actual
normalized errors. Every residual stays visible; no smallness is assumed
in the primary count comparison or signed bound with errors. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace PositiveSharpSourceBound
open PositiveSharpBuchstab PositiveSharpResidual PositiveInteriorModel

theorem model_sub_errors_le_source (X x y s : ℝ) (hX : 1<X)
    (hx : X≤x ∧ x≤2*X) (hy : 0<y ∧ y≤X/2)
    (hm : mesh X≤1/1000000) (hs : 0≤s) :
    model X-residualAbs X x y-deletionTotal X x y≤(sourceTerm X s x y:ℝ)/y := by
  have hc := retained_count_le_source X x y s hX hx hy (by linarith) hs
  have hreal : (orderedCount X x y:ℝ)≤(sourceTerm X s x y:ℝ) := by
    exact_mod_cast hc
  exact (orderedCount_lower X x y hX hm hy.1).trans
    (div_le_div_of_nonneg_right hreal hy.1.le)

theorem eventual_source_lower_with_errors :
    ∃ X₀ : ℝ, 2≤X₀ ∧ ∀ X≥X₀, ∀ x y s : ℝ,
      X≤x → x≤2*X → 0<y → y≤X/2 → 0≤s →
      (141/1000:ℝ)/Real.log X-residualAbs X x y-deletionTotal X x y <
        (sourceTerm X s x y:ℝ)/y := by
  obtain ⟨A,hA,hmodel⟩ := PositiveInteriorModel.eventual_model_lower_reserve
  refine ⟨max A (Real.exp (1000000*Real.log 2)), hA.trans (le_max_left _ _), ?_⟩
  intro X hX x y s hx1 hx2 hy1 hy2 hs
  have hXA : A≤X := (le_max_left _ _).trans hX
  have hX1 : 1<X := by linarith
  have hlog : 1000000*Real.log 2≤Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _)
      ((le_max_right _ _).trans hX)
  have hm : mesh X≤1/1000000 := by
    unfold mesh
    apply (div_le_iff₀ (Real.log_pos hX1)).mpr
    linarith
  have hb := model_sub_errors_le_source X x y s hX1 ⟨hx1,hx2⟩ ⟨hy1,hy2⟩ hm hs
  have hp := hmodel X hXA
  linarith

open SieveWeightedScalarBudget SieveWeightedCutoffs SieveBoxedWeightedMainTerms
open SieveCappedUpperMainTerms (cappedFourth)
open SieveStoppingExpansion

theorem eventually_signed_source_with_errors :
    ∃ s₀ : ℝ, 0<s₀ ∧ s₀≤1/1000 ∧ ∀ s : ℝ, 0<s → s<s₀ →
      ∃ X₀ : ℝ, 1<X₀ ∧ ∀ X≥X₀, ∀ x y : ℝ,
      X≤x → x≤2*X → 0<y → y≤X/2 → ∀ S₂ S₃ : Finset ℕ,
      (∀ p∈S₂, p.Prime ∧ X^(9/35:ℝ)≤(p:ℝ) ∧ (p:ℝ)≤Real.sqrt (2*X)) →
      (∀ p∈S₃, p.Prime ∧ X^alpha s≤(p:ℝ) ∧ (p:ℝ)≤X^(9/35:ℝ)) →
      (3/100:ℝ)*primeEuler (X^alpha s)+(1/1000)/Real.log X-
        residualAbs X x y-deletionTotal X x y <
        SieveBoxedWindow.mainTerm (level X s) s (X^alpha s)-
          boxedMass X s S₂ (cutoffThree X s)-boxedMass X s S₃ (cappedFourth X s)+
            (sourceTerm X s x y:ℝ)/y := by
  obtain ⟨s₀,hs₀,hs1,hb⟩ :=
    SieveSignedBoxedModelPositive.eventually_model_positive_with_reserve
  refine ⟨s₀,hs₀,hs1,?_⟩
  intro s hs hss
  obtain ⟨A,hA,hmain⟩ := hb s hs hss
  refine ⟨max A (Real.exp (1000000*Real.log 2)),hA.trans_le (le_max_left _ _),?_⟩
  intro X hX x y hx1 hx2 hy1 hy2 S₂ S₃ hS₂ hS₃
  have hXA : A≤X := (le_max_left _ _).trans hX
  have hX1 : 1<X := hA.trans_le hXA
  have hlog : 1000000*Real.log 2≤Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _)
      ((le_max_right _ _).trans hX)
  have hm : mesh X≤1/1000000 := by
    unfold mesh
    apply (div_le_iff₀ (Real.log_pos hX1)).mpr
    linarith
  have hcount := model_sub_errors_le_source X x y s hX1 ⟨hx1,hx2⟩ ⟨hy1,hy2⟩ hm hs.le
  have hmodel := hmain X hXA S₂ S₃ hS₂ hS₃
  linarith

run_cmd do
  for decl in [``model_sub_errors_le_source, ``eventual_source_lower_with_errors,
      ``eventually_signed_source_with_errors] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL POSITIVE SOURCE TERM BOUNDED BELOW; EXACT ARITHMETIC ERRORS RETAINED"
end PositiveSharpSourceBound
end
