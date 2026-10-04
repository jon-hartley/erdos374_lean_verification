import PositiveSharpPrimeCriterion
import PositiveSharpRemainderRegularity

/-! The actual prime-free moving-window set is controlled by the literal
residual mean and complete signed remainder second moment. These quantitative
analytic bounds remain premises; only prime-power deletion is discharged. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Set
namespace PositiveSharpExceptionalInput
open PositiveSharpResidual PositiveSharpBoxedCount PositiveSharpErrorMeasure
open PositiveSharpRemainderRegularity

def primeFree (X Y : ℝ) : Set ℝ :=
  {x | ¬∃ p : ℕ, p.Prime ∧ x-x*Y/X<(p:ℝ) ∧ (p:ℝ)≤x} ∩ Icc X (2*X)

theorem primeFree_subset (X s Y : ℝ)
    (hprime : ∀ x∈Icc X (2*X), x∉badSet X Y (1/2000) →
      signedRemainder X s x (x*Y/X)/(x*Y/X)≤(1/2000)/Real.log X →
      ∃ p : ℕ, p.Prime ∧ x-x*Y/X<(p:ℝ) ∧ (p:ℝ)≤x) :
    primeFree X Y⊆badSet X Y (1/2000)∪harmfulSet X s Y (1/2000) := by
  intro x hx
  by_cases he : x∈badSet X Y (1/2000)
  · exact Or.inl he
  · by_cases hr : x∈harmfulSet X s Y (1/2000)
    · exact Or.inr hr
    · exact False.elim (hx.1 (hprime x hx.2 he
        (outside_harmfulSet X s Y (1/2000) x hx.2 hr)))

theorem primeFree_measure_le (X s Y : ℝ)
    (hprime : ∀ x∈Icc X (2*X), x∉badSet X Y (1/2000) →
      signedRemainder X s x (x*Y/X)/(x*Y/X)≤(1/2000)/Real.log X →
      ∃ p : ℕ, p.Prime ∧ x-x*Y/X<(p:ℝ) ∧ (p:ℝ)≤x) :
    volume.real (primeFree X Y)≤volume.real (badSet X Y (1/2000))+
      volume.real (harmfulSet X s Y (1/2000)) := by
  have hu : badSet X Y (1/2000)∪harmfulSet X s Y (1/2000)⊆Icc X (2*X) := by
    intro x hx
    rcases hx with he | hr
    · exact he.2
    · exact hr.2
  exact (measureReal_mono (primeFree_subset X s Y hprime)
    (measure_ne_top_of_subset hu isCompact_Icc.measure_lt_top.ne)).trans
      (measureReal_union_le _ _)

theorem eventually_primeFree_measure_bound :
    ∃ s₀ : ℝ, 0<s₀ ∧ s₀≤1/1000 ∧ ∀ s : ℝ, 0<s → s<s₀ →
      ∃ X₀ : ℝ, 2≤X₀ ∧ ∀ X≥X₀, ∀ Y B_E B_R : ℝ,
      0<Y → Y≤X/4 →
      (∫ x in Icc X (2*X), residualAbs X x (x*Y/X))/X≤B_E →
      (∫ x in Icc X (2*X), (signedRemainder X s x (x*Y/X))^2)/X≤B_R →
      volume.real (primeFree X Y)≤
        X*(2000*Real.log X)*(B_E+4096/X^((1:ℝ)/12))+
        X*(2000*Real.log X/Y)^2*B_R := by
  obtain ⟨s₀,hs₀,hs1,hp⟩ := PositiveSharpPrimeCriterion.eventually_prime_of_error_bounds
  obtain ⟨A,hA,he⟩ := actual_error_measure_bound
  refine ⟨s₀,hs₀,hs1,?_⟩
  intro s hs hss
  obtain ⟨B,_hB,hprime⟩ := hp s hs hss
  refine ⟨max A B, hA.trans (le_max_left _ _), ?_⟩
  intro X hXX Y B_E B_R hY hYX hE hR
  have hXA : A≤X := (le_max_left _ _).trans hXX
  have hXB : B≤X := (le_max_right _ _).trans hXX
  have hX : 1<X := by linarith [hA.trans hXA]
  have hbound := primeFree_measure_le X s Y (fun x hx =>
    hprime X hXB Y x hY hYX hx.1 hx.2)
  have hEbad := he X hXA Y (1/2000) B_E hY (by norm_num) hE
  have hRbad := harmfulSet_measure_le_of_second_moment X s Y (1/2000) B_R
    hX hY (by norm_num) hR
  apply hbound.trans ((add_le_add hEbad hRbad).trans_eq ?_)
  ring

theorem eventually_logarithmic_primeFree_bound :
    ∃ s₀ : ℝ, 0<s₀ ∧ s₀≤1/1000 ∧ ∀ s : ℝ, 0<s → s<s₀ →
      ∃ X₀ : ℝ, 2≤X₀ ∧ ∀ X≥X₀, ∀ Y C_E C_R : ℝ,
      0<Y → Y≤X/4 →
      (∫ x in Icc X (2*X), residualAbs X x (x*Y/X))/X≤C_E/(Real.log X)^2 →
      (∫ x in Icc X (2*X), (signedRemainder X s x (x*Y/X))^2)/X≤
        C_R*Y^2/(Real.log X)^4 →
      volume.real (primeFree X Y)/X≤2000*C_E/Real.log X+
        8192000*Real.log X/X^((1:ℝ)/12)+4000000*C_R/(Real.log X)^2 := by
  obtain ⟨s₀,hs₀,hs1,hp⟩ := eventually_primeFree_measure_bound
  refine ⟨s₀,hs₀,hs1,?_⟩
  intro s hs hss
  obtain ⟨X₀,hX₀,hbound⟩ := hp s hs hss
  refine ⟨X₀,hX₀,?_⟩
  intro X hXX Y C_E C_R hY hYX hE hR
  have hX : 1<X := by linarith [hX₀.trans hXX]
  have hXp : 0<X := by linarith
  have hl : 0<Real.log X := Real.log_pos hX
  have hh := div_le_div_of_nonneg_right
    (hbound X hXX Y (C_E/(Real.log X)^2) (C_R*Y^2/(Real.log X)^4) hY hYX hE hR) hXp.le
  apply hh.trans_eq
  field_simp
  ring

run_cmd do
  for decl in [``primeFree_subset, ``primeFree_measure_le,
      ``eventually_primeFree_measure_bound, ``eventually_logarithmic_primeFree_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL PRIME-FREE MEASURE CONTROLLED BY TWO EXPLICIT ANALYTIC MEAN BOUNDS"
end PositiveSharpExceptionalInput
end
