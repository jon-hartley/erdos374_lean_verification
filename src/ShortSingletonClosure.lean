import ShortSingletonActualMean
import LowerHighClosure

/-! The large short inner singleton mean is discharged. The conditional
Erdős interface now requires the full source residual and the negative mean
of the literal remaining upper rest, with that singleton sector removed. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set

namespace ShortSingletonClosure
open ShortSingletonSector ShortSingletonActualMean ShortSingletonRegularity
open UpperAfter545UpperMean PositiveSharpPowerWindow CancellationTransferCenter

def restNegativeMean (X s Y : ℝ) : ℝ :=
  (∫ x in Icc X (2*X), max (-restRemainder X s (x-x*Y/X) x) 0)/X

theorem rest_integrable (X s Y : ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) :
    IntegrableOn (fun x => restRemainder X s (x-x*Y/X) x) (Icc X (2*X)) := by
  have he : (fun x => restRemainder X s (x-x*Y/X) x) =
      (fun x => UpperAfter545Remaining.upperRemainingRemainder X s (x-x*Y/X) x -
        singletonRemainder X s (x-x*Y/X) x) := by
    funext x
    have hh := upperRemaining_partition X s (x-x*Y/X) x hX hs hs1 hlog
    linarith
  rw [he]
  apply (remaining_upper_integrable X s Y hX hs hs1 hlog).sub
  simpa only [mul_div_assoc] using moving_integrable X s Y hX hs hs1 hlog

theorem upper_negative_le (X s Y : ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) :
    remainingUpperNegativeMean X s Y ≤ absoluteMean X s Y + restNegativeMean X s Y := by
  have hsingle : IntegrableOn (fun x => |singletonRemainder X s (x-x*Y/X) x|)
      (Icc X (2*X)) := by
    simpa only [IntegrableOn, mul_div_assoc] using (moving_integrable X s Y hX hs hs1 hlog).abs
  have hrest := (rest_integrable X s Y hX hs hs1 hlog).neg_part
  have hh := setIntegral_mono_on
    (remaining_upper_negative_integrable X s Y hX hs hs1 hlog)
    (hsingle.add hrest) measurableSet_Icc (fun x (_hx : x ∈ Icc X (2*X)) => by
      have he := upperRemaining_partition X s (x-x*Y/X) x hX hs hs1 hlog
      change max (-UpperAfter545Remaining.upperRemainingRemainder X s (x-x*Y/X) x) 0 ≤
        |singletonRemainder X s (x-x*Y/X) x| + max (-restRemainder X s (x-x*Y/X) x) 0
      apply max_le
      · have ha := neg_le_abs (singletonRemainder X s (x-x*Y/X) x)
        have hr := le_max_left (-restRemainder X s (x-x*Y/X) x) (0:ℝ)
        linarith
      · exact add_nonneg (abs_nonneg _) (le_max_right _ _))
  simp only [Pi.add_apply] at hh
  rw [integral_add hsingle hrest] at hh
  have hd := div_le_div_of_nonneg_right hh (show 0 ≤ X by linarith)
  simpa only [remainingUpperNegativeMean, absoluteMean, restNegativeMean,
    add_div, mul_div_assoc, one_div, div_eq_mul_inv, mul_add, mul_one,
    mul_assoc, mul_comm, mul_left_comm] using hd

theorem eventually_upper_negative_of_rest (s C : ℝ) (A : ℕ)
    (hs : 0 < s) (hs1 : s ≤ 1/1000)
    (hrest : ∀ᶠ X : ℝ in atTop,
      restNegativeMean X s (halfWidth X (101/1000)) ≤
        C*halfWidth X (101/1000)/(Real.log X)^A) :
    ∀ᶠ X : ℝ in atTop,
      remainingUpperNegativeMean X s (halfWidth X (101/1000)) ≤
        (C+1)*halfWidth X (101/1000)/(Real.log X)^A := by
  filter_upwards [eventually_absolute_log s A hs hs1, hrest] with X hsng hrem
  calc
    _ ≤ absoluteMean X s (halfWidth X (101/1000)) +
        restNegativeMean X s (halfWidth X (101/1000)) :=
      upper_negative_le X s _ hsng.1 hs hs1 hsng.2.1
    _ ≤ halfWidth X (101/1000)/(Real.log X)^A +
        C*halfWidth X (101/1000)/(Real.log X)^A := add_le_add hsng.2.2 hrem
    _ = _ := by ring

theorem eventually_erdos_conclusions_of_source_and_rest_negative_mean :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/1000 ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∀ C_E C_R : ℝ,
      (∀ᶠ X : ℝ in atTop,
        (∫ x in Icc X (2*X), sourceResidualAbs X x (x*halfWidth X (101/1000)/X))/X ≤
          C_E/(Real.log X)^2) →
      (∀ᶠ X : ℝ in atTop,
        restNegativeMean X s (halfWidth X (101/1000)) ≤
          C_R*halfWidth X (101/1000)/(Real.log X)^2) →
      Erdos374.MainStatement ∧
      Erdos374.PositiveLowerDensity LiteratureReduction.MinimumSix ∧
      ∃ c : ℝ, 0 < c ∧ ∃ cutoff : ℕ, ∀ N : ℕ, cutoff ≤ N →
        c*(N:ℝ) ≤ (Erdos374.prefixCount LiteratureReduction.MinimumSix N:ℝ) := by
  obtain ⟨s₀,hs₀,hs1,hp⟩ :=
    LowerHighClosure.eventually_erdos_conclusions_of_source_and_upper_negative_mean
  refine ⟨s₀,hs₀,hs1,?_⟩
  intro s hs hss C_E C_R hE hR
  apply hp s hs hss C_E (C_R+1) hE
  exact eventually_upper_negative_of_rest s C_R 2 hs (hss.le.trans hs1) hR

run_cmd do
  for decl in [``rest_integrable, ``upper_negative_le, ``eventually_upper_negative_of_rest,
      ``eventually_erdos_conclusions_of_source_and_rest_negative_mean] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "SHORT SINGLETON MEAN DISCHARGED; FULL SOURCE AND UPPER REST MEAN REMAIN EXPLICIT"

end ShortSingletonClosure
