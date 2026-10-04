import DirectMovingPhysicalMean

/-! The conditional Erdős endpoint with the complete high physical cutoff
raised to .545. Both sourceResidualAbs and highNegativeMean remain premises. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Filter MeasureTheory Set

namespace DirectMovingPhysicalClosure
open TailRemainderBand TailRemainderMean PositiveSharpPowerWindow
open CancellationTransferCenter

theorem eventually_full_negative_of_high (s C : ℝ) (A : ℕ)
    (hs : 0<s) (hs1 : s≤1/1000)
    (hhigh : ∀ᶠ X : ℝ in atTop,
      highNegativeMean X s (109/200) (halfWidth X (101/1000))≤
        C*halfWidth X (101/1000)/(Real.log X)^A) :
    ∀ᶠ X : ℝ in atTop,
      negativeMean X s (halfWidth X (101/1000))≤
        (C+1)*halfWidth X (101/1000)/(Real.log X)^A := by
  filter_upwards [DirectMovingPhysicalMean.eventually_absolute_log s A hs hs1,hhigh]
    with X hl hh
  have he : (C+1)*halfWidth X (101/1000)/(Real.log X)^A=
      halfWidth X (101/1000)/(Real.log X)^A+
        C*halfWidth X (101/1000)/(Real.log X)^A := by ring
  rw [he]
  exact (negativeMean_le_low_add_high X s (109/200) (halfWidth X (101/1000))
    (by linarith [hl.1])).trans (add_le_add hl.2 hh)

theorem eventually_erdos_conclusions_of_source_and_high_negative_mean :
    ∃s₀:ℝ, 0<s₀ ∧ s₀≤1/1000 ∧ ∀s:ℝ, 0<s → s<s₀ →
      ∀C_E C_N:ℝ,
      (∀ᶠ X:ℝ in atTop,
        (∫x in Icc X (2*X), sourceResidualAbs X x (x*halfWidth X (101/1000)/X))/X≤
          C_E/(Real.log X)^2) →
      (∀ᶠ X:ℝ in atTop,
        highNegativeMean X s (109/200) (halfWidth X (101/1000))≤
          C_N*halfWidth X (101/1000)/(Real.log X)^2) →
      Erdos374.MainStatement ∧
      Erdos374.PositiveLowerDensity LiteratureReduction.MinimumSix ∧
      ∃c:ℝ, 0<c ∧ ∃cutoff:ℕ, ∀N:ℕ, cutoff≤N →
        c*(N:ℝ)≤(Erdos374.prefixCount LiteratureReduction.MinimumSix N:ℝ) := by
  obtain ⟨s₀,hs₀,hs1,hp⟩ :=
    TailErdosClosure.eventually_erdos_conclusions_of_source_and_negative_mean
  refine ⟨s₀,hs₀,hs1,?_⟩
  intro s hs hss C_E C_N hE hN
  apply hp s hs hss C_E (C_N+1) hE
  exact eventually_full_negative_of_high s C_N 2 hs (hss.le.trans hs1) hN

run_cmd do
  for decl in [``eventually_full_negative_of_high,
      ``eventually_erdos_conclusions_of_source_and_high_negative_mean] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "CONDITIONAL ERDOS ENDPOINT AT HIGH CUTOFF .545; BOTH ANALYTIC PREMISES EXPLICIT"

end DirectMovingPhysicalClosure
