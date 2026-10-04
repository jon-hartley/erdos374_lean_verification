import SieveFineProfileTransfer
import UpperProfileCertificate
import SieveUpperSelectedWindow

/-! Concrete actual upper selector from the fully checked fine-grid
certificate. The resulting prime-window bound retains its exact arithmetic
remainder; no remainder estimate or positive prime count is concluded. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open Real
open scoped BigOperators
namespace SieveUpperCertified
open SieveFineProfileStructure

theorem certified_differences (j : ℕ) (hj : j < 720) :
    0 ≤ coefficient UpperProfileCertificate.value j :=
  UpperProfileCertificate.coefficient_nonneg ⟨j, hj⟩

theorem certified_rows (i : ℕ) (hi : i < 720) :
    SieveFineProfileTransfer.rowBudget UpperProfileCertificate.value i ≤
      UpperProfileCertificate.value i := by
  have h := UpperProfileCertificate.rowBudget ⟨i, hi⟩
  simpa only [SieveFineProfileTransfer.rowBudget, coefficient,
    UpperProfileCertificate.coefficient, mul_comm] using h

theorem certified_area :
    (∑ j ∈ Finset.range 720, UpperProfileCertificate.value j)/40 ≤ (307/500:ℝ) := by
  rw [← area_eq UpperProfileCertificate.value UpperProfileCertificate.value_terminal]
  exact UpperProfileCertificate.finite_area_lt.le

theorem actual_postfixed : SieveProfileSupersolution.Postfixed
    (profile UpperProfileCertificate.value) :=
  SieveFineProfileTransfer.actual_postfixed UpperProfileCertificate.value
    certified_differences UpperProfileCertificate.value_terminal certified_rows

theorem eventual_lower_profile (ε : ℝ) (hε : 0 < ε) :
    SieveEventualProfile.EventualProfile
      (fun r => profile UpperProfileCertificate.value r+ε*exp (-r)) :=
  SieveProfileSupersolution.bootstrap (profile UpperProfileCertificate.value)
    (fun r _ => profile_nonneg _ certified_differences r)
    (profile_tail _ certified_differences) actual_postfixed ε hε

theorem eventual_full_upper :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^3 ≤ T →
      SieveFullCutoffTransfer.fullUpper T z ≤
        (452/375:ℝ)*SieveStoppingExpansion.primeEuler z :=
  SieveFineProfileTransfer.eventual_upper_bound UpperProfileCertificate.value
    certified_differences UpperProfileCertificate.value_terminal certified_rows certified_area

/-- A literal prime-window upper bound with the complete signed arithmetic
remainder retained. No estimate on that remainder is assumed. -/
theorem eventual_prime_window_upper :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^3 ≤ T →
      ∀ L y : ℝ, z ≤ L → 0 ≤ y →
      ((FiniteSieveWindow.primeWindow L (L+y)).card : ℝ) ≤
        (452/375:ℝ)*y*SieveStoppingExpansion.primeEuler z+
          SieveUpperSelectedWindow.remainder T z L (L+y) := by
  obtain ⟨Z, hZ, hb⟩ := eventual_full_upper
  refine ⟨Z, hZ, ?_⟩
  intro z T hz hT L y hzL hy
  have hz2 : 2 ≤ z := hZ.trans hz
  exact SieveUpperSelectedWindow.prime_window_le_of_fullUpper T z L y (452/375)
    (by linarith) hy hzL (hb z T hz hT)

run_cmd do
  for decl in [``certified_differences, ``certified_rows, ``certified_area,
      ``actual_postfixed, ``eventual_lower_profile, ``eventual_full_upper,
      ``eventual_prime_window_upper] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "UNCONDITIONAL ACTUAL FULL UPPER SELECTOR AT MOST (452/375)*V"
end SieveUpperCertified
end
