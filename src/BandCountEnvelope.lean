import SupremumMoment
import PolynomialLogEnvelope

/-!
The dyadic amplitude-band count is logarithmic when the cutoff is
bounded below by a fixed constant times X^(-2).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter

namespace BandCountEnvelope
open SupremumMoment

theorem logarithmic_bound (v U X c : ℝ) (hX : 1 ≤ X) (hc : 0 < c) (hc1 : c ≤ 1)
    (hv : c / X ^ 2 ≤ v) (hU : U ≤ 1) :
    bandCountBound v U ≤ (1 + (2 - Real.log c) / Real.log 2) * (1 + Real.log X) := by
  have hXp : 0 < X := by linarith
  have hvp : 0 < v := (div_pos hc (by positivity)).trans_le hv
  have hXsq : 1 ≤ X ^ 2 := one_le_pow₀ hX
  have hratio : U / v ≤ X ^ 2 / c := by
    apply (div_le_div_iff₀ hvp hc).mpr
    have hh := (div_le_iff₀ (by positivity : 0 < X ^ 2)).mp hv
    nlinarith [mul_le_mul_of_nonneg_right hU hc.le]
  have hone : 1 ≤ X ^ 2 / c := (one_le_div hc).mpr (hc1.trans hXsq)
  have hmax : max (U / v) 1 ≤ X ^ 2 / c := max_le hratio hone
  have hlog := Real.log_le_log (show 0 < max (U / v) 1 by
    have hh := le_max_right (U / v) 1; linarith) hmax
  rw [Real.log_div (by positivity) hc.ne', Real.log_pow] at hlog
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hlc : Real.log c ≤ 0 := Real.log_nonpos hc.le hc1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold bandCountBound
  have hstep := div_le_div_of_nonneg_right hlog hl2.le
  apply (add_le_add (le_refl (1 : ℝ)) hstep).trans
  apply (mul_le_mul_iff_right₀ hl2).mp
  field_simp
  norm_num only [Nat.cast_ofNat]
  nlinarith [mul_nonneg (neg_nonneg.mpr hlc) hlX, mul_nonneg hl2.le hlX]

theorem eventually_bound (c δ : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hδ : 0 < δ) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧ ∀ v U : ℝ,
      c / X ^ 2 ≤ v → U ≤ 1 → bandCountBound v U ≤ X ^ δ := by
  have hlc : Real.log c ≤ 0 := Real.log_nonpos hc.le hc1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 ≤ 1 + (2 - Real.log c) / Real.log 2 := by
    have hh : 0 ≤ 2 - Real.log c := by linarith
    positivity
  filter_upwards [PolynomialLogEnvelope.eventually_bound
    (1 + (2 - Real.log c) / Real.log 2) 1 δ hC hδ] with X hX
  refine ⟨hX.1, ?_⟩
  intro v U hv hU
  exact (logarithmic_bound v U X c hX.1 hc hc1 hv hU).trans (by simpa using hX.2)

end BandCountEnvelope

#print axioms BandCountEnvelope.eventually_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``BandCountEnvelope.eventually_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "BAND COUNT ENVELOPE PASSED"
