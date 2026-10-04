import MomentRemainderReduction
import MomentRemainderSupport
import PositiveSharpErdosClosure

/-! The remaining signed-remainder estimate is confined to actual physical
indices X^0.1 < m < X^(1-2s). This file does not prove that estimate or the
residual estimate. Both remain explicit in the final conditional theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter MeasureTheory Set

namespace MomentRemainderBand
open MomentSmallRemainder PositiveSharpPowerWindow PositiveSharpResidual

theorem eventually_remaining_indices (s ε : ℝ) (hs : 0<s) (hs1 : s≤1/1000) (hε : 0<ε) :
    ∀ᶠ X:ℝ in atTop, 1<X ∧ ∀m∈highSupport X s (1/10),
      X^((1:ℝ)/10)<(m:ℝ) ∧ (m:ℝ)<X^(1-2*s) ∧
        |PositiveSharpRemainderAnalysisPhysical.coefficient X s m|≤X^ε := by
  filter_upwards [MomentRemainderSupport.eventually_support_and_coefficient s ε hs hs1 hε]
    with X hc
  refine ⟨hc.1,?_⟩
  intro m hm
  obtain ⟨hm, hcut⟩ := Finset.mem_filter.mp hm
  exact ⟨lt_of_not_ge hcut, (hc.2 m hm).2.1, (hc.2 m hm).2.2⟩

theorem eventually_erdos_conclusions_of_residual_and_band_means :
    ∃ s₀ : ℝ, 0<s₀ ∧ s₀≤1/1000 ∧ ∀s:ℝ, 0<s → s<s₀ →
      ∀C_E C_H:ℝ,
      (∀ᶠ X:ℝ in atTop,
        (∫x in Icc X (2*X), residualAbs X x (x*halfWidth X (101/1000)/X))/X≤
          C_E/(Real.log X)^2) →
      (∀ᶠ X:ℝ in atTop,
        (∫x in Icc X (2*X),
          (high X s (1/10) x (x*halfWidth X (101/1000)/X))^2)/X≤
            C_H*(halfWidth X (101/1000))^2/(Real.log X)^4) →
      Erdos374.MainStatement ∧
      Erdos374.PositiveLowerDensity LiteratureReduction.MinimumSix ∧
      ∃c:ℝ, 0<c ∧ ∃cutoff:ℕ, ∀N:ℕ, cutoff≤N →
        c*(N:ℝ)≤(Erdos374.prefixCount LiteratureReduction.MinimumSix N:ℝ) := by
  obtain ⟨s₀,hs₀,hs1,hb⟩ := PositiveSharpErdosClosure.eventually_erdos_conclusions_of_means
  refine ⟨s₀,hs₀,hs1,?_⟩
  intro s hs hss C_E C_H hE hH
  apply hb s hs hss C_E (2+2*C_H) hE
  exact MomentRemainderReduction.eventually_full_mean_of_high s (1/10) (101/1000)
    C_H 4 hs (hss.le.trans hs1) (by norm_num) (by norm_num) hH

run_cmd do
  for decl in [``eventually_remaining_indices,
      ``eventually_erdos_conclusions_of_residual_and_band_means] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "REMAINDER BAND REDUCED; RESIDUAL AND BAND MEANS REMAIN OPEN"

end MomentRemainderBand
