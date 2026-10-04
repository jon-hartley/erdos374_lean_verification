import TailPrimeFree
import PositiveSharpErdosClosure
import CancellationTransferResidual

/-! Alternative exact closure through one-sided first moments. The actual
signed bias discharges the positive/negative exchange, but neither one-sided
saving nor the source residual mean is proved here. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter MeasureTheory Set
namespace TailErdosClosure
open TailRemainderMean PositiveSharpPowerWindow PositiveSharpResidual
open PositiveSharpErdosReduction CancellationTransferCenter
open Erdos374.HarmanAnalytic151Orientation Erdos374.HarmanDyadic151

theorem budget_tendsto_zero (C_E C_P : ℝ) :
    Tendsto (fun X:ℝ => 2000*(C_E+C_P)/Real.log X+
      8192000*Real.log X/X^((1:ℝ)/12)) atTop (nhds 0) := by
  simpa only [mul_zero,zero_div,add_zero] using
    PositiveSharpPowerWindow.budget_tendsto_zero (C_E+C_P) 0

theorem eventually_power_density_zero_positive (β : ℝ) (hβ : 0≤β) (hβ1 : β<1) :
    ∃s₀:ℝ, 0<s₀ ∧ s₀≤1/1000 ∧ ∀s:ℝ, 0<s → s<s₀ →
      ∀C_E C_P:ℝ,
      (∀ᶠ X:ℝ in atTop,
        (∫x in Icc X (2*X), residualAbs X x (x*halfWidth X β/X))/X≤C_E/(Real.log X)^2) →
      (∀ᶠ X:ℝ in atTop,
        positiveMean X s (halfWidth X β)≤C_P*halfWidth X β/(Real.log X)^2) →
      Tendsto (fun X:ℝ => volume.real (powerPrimeFree X β)/X) atTop (nhds 0) := by
  obtain ⟨s₀,hs₀,hs1,hp⟩ := TailPrimeFree.eventually_logarithmic_primeFree_bound
  refine ⟨s₀,hs₀,hs1,?_⟩
  intro s hs hss C_E C_P hE hP
  obtain ⟨X₀,hX₀,hbound⟩ := hp s hs hss
  have hn : ∀ᶠ X:ℝ in atTop, 0≤volume.real (powerPrimeFree X β)/X := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
    exact div_nonneg ENNReal.toReal_nonneg hX.le
  have hu : ∀ᶠ X:ℝ in atTop, volume.real (powerPrimeFree X β)/X≤
      2000*(C_E+C_P)/Real.log X+8192000*Real.log X/X^((1:ℝ)/12) := by
    filter_upwards [hE,hP,eventually_ge_atTop X₀,halfWidth_eventually β hβ1]
      with X hEX hPX hXX hY
    have hX : 0<X := by linarith [hX₀.trans hXX]
    exact (div_le_div_of_nonneg_right (powerPrimeFree_measure_le X β hX hβ) hX.le).trans
      (hbound X hXX (halfWidth X β) C_E C_P hY.1 hY.2 hEX hPX)
  exact squeeze_zero' hn hu (budget_tendsto_zero C_E C_P)

theorem erdos_conclusions_of_power_density
    (hlimit : Tendsto (fun X:ℝ => volume.real (powerPrimeFree X (101/1000))/X)
      atTop (nhds 0)) :
    Erdos374.MainStatement ∧
    Erdos374.PositiveLowerDensity LiteratureReduction.MinimumSix ∧
    ∃c:ℝ, 0<c ∧ ∃cutoff:ℕ, ∀N:ℕ, cutoff≤N →
      c*(N:ℝ)≤(Erdos374.prefixCount LiteratureReduction.MinimumSix N:ℝ) := by
  have hprime := seed_exceptional_of_power_density hlimit
  have hsamp := PositiveSharpErdosClosure.polynomial_sampling
  have hdensity := LiteratureReduction.positive_lower_density_from_published_interfaces hprime hsamp
  exact ⟨Erdos374.AnalyticClosure151.candidate_main_from_backward151
    (backward_prefix_from_dyadic151 hprime) hsamp,hdensity,
    LiteratureReduction.counting_bound_of_positiveLowerDensity _ hdensity⟩

theorem eventually_erdos_conclusions_of_positive_mean :
    ∃s₀:ℝ, 0<s₀ ∧ s₀≤1/1000 ∧ ∀s:ℝ, 0<s → s<s₀ →
      ∀C_E C_P:ℝ,
      (∀ᶠ X:ℝ in atTop,
        (∫x in Icc X (2*X), residualAbs X x (x*halfWidth X (101/1000)/X))/X≤
          C_E/(Real.log X)^2) →
      (∀ᶠ X:ℝ in atTop,
        positiveMean X s (halfWidth X (101/1000))≤
          C_P*halfWidth X (101/1000)/(Real.log X)^2) →
      Erdos374.MainStatement ∧
      Erdos374.PositiveLowerDensity LiteratureReduction.MinimumSix ∧
      ∃c:ℝ, 0<c ∧ ∃cutoff:ℕ, ∀N:ℕ, cutoff≤N →
        c*(N:ℝ)≤(Erdos374.prefixCount LiteratureReduction.MinimumSix N:ℝ) := by
  obtain ⟨s₀,hs₀,hs1,hp⟩ := eventually_power_density_zero_positive
    (101/1000) (by norm_num) (by norm_num)
  exact ⟨s₀,hs₀,hs1,fun s hs hss C_E C_P hE hP =>
    erdos_conclusions_of_power_density (hp s hs hss C_E C_P hE hP)⟩

theorem eventually_erdos_conclusions_of_negative_mean :
    ∃s₀:ℝ, 0<s₀ ∧ s₀≤1/1000 ∧ ∀s:ℝ, 0<s → s<s₀ →
      ∀C_E C_N:ℝ,
      (∀ᶠ X:ℝ in atTop,
        (∫x in Icc X (2*X), residualAbs X x (x*halfWidth X (101/1000)/X))/X≤
          C_E/(Real.log X)^2) →
      (∀ᶠ X:ℝ in atTop,
        negativeMean X s (halfWidth X (101/1000))≤
          C_N*halfWidth X (101/1000)/(Real.log X)^2) →
      Erdos374.MainStatement ∧
      Erdos374.PositiveLowerDensity LiteratureReduction.MinimumSix ∧
      ∃c:ℝ, 0<c ∧ ∃cutoff:ℕ, ∀N:ℕ, cutoff≤N →
        c*(N:ℝ)≤(Erdos374.prefixCount LiteratureReduction.MinimumSix N:ℝ) := by
  obtain ⟨s₀,hs₀,hs1,hp⟩ := eventually_erdos_conclusions_of_positive_mean
  refine ⟨s₀,hs₀,hs1,?_⟩
  intro s hs hss C_E C_N hE hN
  apply hp s hs hss C_E (C_N+1) hE
  filter_upwards [hN,eventually_positive_of_negative s C_N 2 hs (hss.le.trans hs1),
    halfWidth_eventually (101/1000) (by norm_num)] with X hn hb hY
  exact (hb.2 _ hY.1.le (by linarith [hb.1,hY.2]) hn).1

theorem eventually_erdos_conclusions_of_source_and_negative_mean :
    ∃s₀:ℝ, 0<s₀ ∧ s₀≤1/1000 ∧ ∀s:ℝ, 0<s → s<s₀ →
      ∀C_E C_N:ℝ,
      (∀ᶠ X:ℝ in atTop,
        (∫x in Icc X (2*X), sourceResidualAbs X x (x*halfWidth X (101/1000)/X))/X≤
          C_E/(Real.log X)^2) →
      (∀ᶠ X:ℝ in atTop,
        negativeMean X s (halfWidth X (101/1000))≤
          C_N*halfWidth X (101/1000)/(Real.log X)^2) →
      Erdos374.MainStatement ∧
      Erdos374.PositiveLowerDensity LiteratureReduction.MinimumSix ∧
      ∃c:ℝ, 0<c ∧ ∃cutoff:ℕ, ∀N:ℕ, cutoff≤N →
        c*(N:ℝ)≤(Erdos374.prefixCount LiteratureReduction.MinimumSix N:ℝ) := by
  obtain ⟨s₀,hs₀,hs1,hp⟩ := eventually_erdos_conclusions_of_negative_mean
  refine ⟨s₀,hs₀,hs1,?_⟩
  intro s hs hss C_E C_N hE hN
  apply hp s hs hss (C_E+1) C_N _ hN
  filter_upwards [hE,CancellationTransferResidual.eventually_residual_transfer_log 2,
    halfWidth_eventually (101/1000) (by norm_num)] with X he hb hY
  have hd := (abs_le.mp (hb.2 _ hY.1)).2
  have hid : (C_E+1)/(Real.log X)^2=C_E/(Real.log X)^2+1/(Real.log X)^2 := by ring
  rw [hid]
  linarith

run_cmd do
  for decl in [``budget_tendsto_zero,``eventually_power_density_zero_positive,
      ``erdos_conclusions_of_power_density,``eventually_erdos_conclusions_of_positive_mean,
      ``eventually_erdos_conclusions_of_negative_mean,
      ``eventually_erdos_conclusions_of_source_and_negative_mean] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ERDOS ENDPOINT REDUCED TO SOURCE RESIDUAL AND ONE-SIDED FIRST MOMENT; BOTH SAVINGS OPEN"
end TailErdosClosure
end
