import PositiveSharpPowerWindow
import LiteratureReduction

/-! The literal two moment estimates imply the seed's exact exceptional-set
input. The complete factorial conclusion additionally retains the seed's
explicit sampling premise: the separate MangoldtCancellation source is
outside the verified predecessor closure and is not imported here. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter MeasureTheory Set

namespace PositiveSharpErdosReduction
open PositiveSharpPowerWindow PositiveSharpResidual PositiveSharpBoxedCount
open Erdos374.HarmanAnalytic151Orientation Erdos374.HarmanDyadic151

theorem seed_bad_subset (X : ℝ) (hX : 1≤X) :
    realBackwardBad151 ∩ Icc X (2*X) ⊆ powerPrimeFree X (101/1000) := by
  intro x hx
  refine ⟨?_,hx.2⟩
  intro hp
  obtain ⟨p,hp,hleft,hright⟩ := hp
  apply hx.1
  refine ⟨p,hp,hright,?_⟩
  have hpow : x^(101/1000:ℝ)≤x^backwardExponent151 :=
    Real.rpow_le_rpow_of_exponent_le (hX.trans hx.2.1)
      (by norm_num [backwardExponent151])
  linarith

/-- The retained endpoint asks for o(X), not a power-saving exceptional rate. -/
theorem seed_exceptional_of_power_density
    (hlimit : Tendsto (fun X : ℝ => volume.real (powerPrimeFree X (101/1000))/X)
      atTop (nhds 0)) : RealBackwardDyadicExceptionalMeasure151 := by
  intro ε hε
  obtain ⟨A,hA⟩ := eventually_atTop.mp (hlimit.eventually_lt_const hε)
  refine ⟨max A 1,?_⟩
  intro X hXX
  have hX : 1≤X := (le_max_right _ _).trans hXX
  have hXp : 0<X := by linarith
  have hsmall := (div_lt_iff₀ hXp).mp (hA X ((le_max_left _ _).trans hXX))
  calc
    _ ≤ volume.real (powerPrimeFree X (101/1000)) :=
      measureReal_mono (seed_bad_subset X hX)
        (measure_ne_top_of_subset inter_subset_right isCompact_Icc.measure_lt_top.ne)
    _ ≤ ε*X := hsmall.le

theorem eventually_seed_exceptional_of_means :
    ∃ s₀ : ℝ, 0<s₀ ∧ s₀≤1/1000 ∧ ∀ s : ℝ, 0<s → s<s₀ →
      ∀ C_E C_R : ℝ,
      (∀ᶠ X : ℝ in atTop,
        (∫ x in Icc X (2*X), residualAbs X x (x*halfWidth X (101/1000)/X))/X≤
          C_E/(Real.log X)^2) →
      (∀ᶠ X : ℝ in atTop,
        (∫ x in Icc X (2*X),
          (signedRemainder X s x (x*halfWidth X (101/1000)/X))^2)/X≤
          C_R*(halfWidth X (101/1000))^2/(Real.log X)^4) →
      RealBackwardDyadicExceptionalMeasure151 := by
  obtain ⟨s₀,hs₀,hs1,hb⟩ := eventually_power_primeFree_density_zero
    (101/1000) (by norm_num) (by norm_num)
  refine ⟨s₀,hs₀,hs1,?_⟩
  intro s hs hss C_E C_R hE hR
  exact seed_exceptional_of_power_density (hb s hs hss C_E C_R hE hR)

/-- No prime-interval input is separately assumed: it is derived from the
two literal moments. Sampling remains a third, explicitly stated input. -/
theorem eventually_erdos_conclusions_of_means_and_sampling :
    ∃ s₀ : ℝ, 0<s₀ ∧ s₀≤1/1000 ∧ ∀ s : ℝ, 0<s → s<s₀ →
      ∀ C_E C_R : ℝ,
      (∀ᶠ X : ℝ in atTop,
        (∫ x in Icc X (2*X), residualAbs X x (x*halfWidth X (101/1000)/X))/X≤
          C_E/(Real.log X)^2) →
      (∀ᶠ X : ℝ in atTop,
        (∫ x in Icc X (2*X),
          (signedRemainder X s x (x*halfWidth X (101/1000)/X))^2)/X≤
          C_R*(halfWidth X (101/1000))^2/(Real.log X)^4) →
      Erdos374.SamplingPolynomial149.PolynomialReciprocalPrimeSampling →
      Erdos374.MainStatement ∧
      Erdos374.PositiveLowerDensity LiteratureReduction.MinimumSix ∧
      ∃ c : ℝ, 0<c ∧ ∃ cutoff : ℕ, ∀ N : ℕ, cutoff≤N →
        c*(N:ℝ)≤(Erdos374.prefixCount LiteratureReduction.MinimumSix N:ℝ) := by
  obtain ⟨s₀,hs₀,hs1,hb⟩ := eventually_seed_exceptional_of_means
  refine ⟨s₀,hs₀,hs1,?_⟩
  intro s hs hss C_E C_R hE hR hsampling
  have hprime := hb s hs hss C_E C_R hE hR
  have hdensity := LiteratureReduction.positive_lower_density_from_published_interfaces
    hprime hsampling
  exact ⟨Erdos374.AnalyticClosure151.candidate_main_from_backward151
    (backward_prefix_from_dyadic151 hprime) hsampling, hdensity,
    LiteratureReduction.counting_bound_of_positiveLowerDensity _ hdensity⟩

run_cmd do
  for decl in [``seed_bad_subset, ``seed_exceptional_of_power_density,
      ``eventually_seed_exceptional_of_means,
      ``eventually_erdos_conclusions_of_means_and_sampling] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXACT SEED EXCEPTIONAL ADAPTER; ERDOS CONCLUSION CONDITIONAL ON TWO MOMENTS AND SAMPLING"
end PositiveSharpErdosReduction
end
