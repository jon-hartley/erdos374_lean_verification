import LowerHighMean
import UpperAfter545UpperMean
import DirectMovingPhysicalClosure

/-! The lower high physical mean is discharged. The only remaining mean
premises at this interface are the actual upper kernels and sourceResidualAbs. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter MeasureTheory Set

namespace LowerHighClosure
open PositiveSharpPowerWindow UpperAfter545UpperMean CancellationTransferCenter

theorem eventually_lower_high_absolute_log (s : ℝ) (A : ℕ)
    (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X:ℝ in atTop,
      lowerHighAbsoluteMean X s (halfWidth X (101/1000))≤
        halfWidth X (101/1000)/(Real.log X)^A := by
  filter_upwards [LowerHighMean.eventually_absolute_log s A hs hs1] with X hx
  simpa only [lowerHighAbsoluteMean,LowerHighMean.absoluteMean,
    one_div,div_eq_mul_inv,mul_comm,mul_one,one_mul] using hx.2

theorem eventually_high_negative_of_upper (s C : ℝ) (A : ℕ)
    (hs : 0<s) (hs1 : s≤1/1000)
    (hu : ∀ᶠ X:ℝ in atTop,
      remainingUpperNegativeMean X s (halfWidth X (101/1000))≤
        C*halfWidth X (101/1000)/(Real.log X)^A) :
    ∀ᶠ X:ℝ in atTop,
      TailRemainderBand.highNegativeMean X s (109/200) (halfWidth X (101/1000))≤
        (C+1)*halfWidth X (101/1000)/(Real.log X)^A := by
  have hl : ∀ᶠ X:ℝ in atTop,
      lowerHighAbsoluteMean X s (halfWidth X (101/1000))≤
        1*halfWidth X (101/1000)/(Real.log X)^A := by
    simpa only [one_mul] using eventually_lower_high_absolute_log s A hs hs1
  simpa only [add_comm (1:ℝ) C] using
    eventually_highNegativeMean_of_bounds s 1 C A
      (fun X => halfWidth X (101/1000)) hs hs1 hl hu

theorem eventually_erdos_conclusions_of_source_and_upper_negative_mean :
    ∃s₀:ℝ, 0<s₀ ∧ s₀≤1/1000 ∧ ∀s:ℝ, 0<s → s<s₀ →
      ∀C_E C_U:ℝ,
      (∀ᶠ X:ℝ in atTop,
        (∫x in Icc X (2*X),sourceResidualAbs X x (x*halfWidth X (101/1000)/X))/X≤
          C_E/(Real.log X)^2) →
      (∀ᶠ X:ℝ in atTop,
        remainingUpperNegativeMean X s (halfWidth X (101/1000))≤
          C_U*halfWidth X (101/1000)/(Real.log X)^2) →
      Erdos374.MainStatement ∧
      Erdos374.PositiveLowerDensity LiteratureReduction.MinimumSix ∧
      ∃c:ℝ, 0<c ∧ ∃cutoff:ℕ, ∀N:ℕ, cutoff≤N →
        c*(N:ℝ)≤(Erdos374.prefixCount LiteratureReduction.MinimumSix N:ℝ) := by
  obtain ⟨s₀,hs₀,hs1,hp⟩ :=
    DirectMovingPhysicalClosure.eventually_erdos_conclusions_of_source_and_high_negative_mean
  refine ⟨s₀,hs₀,hs1,?_⟩
  intro s hs hss C_E C_U hE hU
  apply hp s hs hss C_E (C_U+1) hE
  exact eventually_high_negative_of_upper s C_U 2 hs (hss.le.trans hs1) hU

run_cmd do
  for decl in [``eventually_lower_high_absolute_log,``eventually_high_negative_of_upper,
      ``eventually_erdos_conclusions_of_source_and_upper_negative_mean] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "LOWER HIGH MEAN DISCHARGED; CONDITIONAL ERDOS NEEDS FULL SOURCE AND ACTUAL REMAINING UPPER MEAN"

end LowerHighClosure
