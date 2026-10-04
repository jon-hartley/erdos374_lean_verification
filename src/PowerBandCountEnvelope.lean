import BandCountEnvelope

/-!
Extend the amplitude-band helper to arbitrary fixed powers. The cutoff
may be as small as c/X^a and the supremum may grow as X^b. Their ratio
still produces only a logarithmic band count.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter

namespace BandCountEnvelope
open SupremumMoment

theorem logarithmic_bound_of_powers (v U X c a b : ℝ)
    (hX : 1 ≤ X) (hc : 0 < c) (hc1 : c ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hv : c / X ^ a ≤ v) (hU : U ≤ X ^ b) :
    bandCountBound v U ≤
      (1 + (a + b - Real.log c) / Real.log 2) * (1 + Real.log X) := by
  have hXp : 0 < X := by linarith
  have hvp : 0 < v := (div_pos hc (by positivity)).trans_le hv
  have hratio : U / v ≤ X ^ (a + b) / c := by
    apply (div_le_div_iff₀ hvp hc).mpr
    have hh := (div_le_iff₀ (Real.rpow_pos_of_pos hXp a)).mp hv
    calc
      U * c ≤ X ^ b * c := mul_le_mul_of_nonneg_right hU hc.le
      _ ≤ X ^ b * (v * X ^ a) := mul_le_mul_of_nonneg_left hh (by positivity)
      _ = X ^ (a + b) * v := by rw [Real.rpow_add hXp]; ring
  have hone : 1 ≤ X ^ (a + b) / c :=
    (one_le_div hc).mpr (hc1.trans (Real.one_le_rpow hX (by linarith)))
  have hmax : max (U / v) 1 ≤ X ^ (a + b) / c := max_le hratio hone
  have hlog := Real.log_le_log (show 0 < max (U / v) 1 by
    have hh := le_max_right (U / v) 1; linarith) hmax
  rw [Real.log_div (by positivity) hc.ne', Real.log_rpow hXp] at hlog
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hlc : Real.log c ≤ 0 := Real.log_nonpos hc.le hc1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold bandCountBound
  have hstep := div_le_div_of_nonneg_right hlog hl2.le
  apply (add_le_add (le_refl (1 : ℝ)) hstep).trans
  apply (mul_le_mul_iff_right₀ hl2).mp
  field_simp
  nlinarith [mul_nonneg (neg_nonneg.mpr hlc) hlX, mul_nonneg hl2.le hlX]

theorem eventually_bound_of_powers (c a b δ : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 < δ) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧ ∀ v U : ℝ,
      c / X ^ a ≤ v → U ≤ X ^ b → bandCountBound v U ≤ X ^ δ := by
  have hlc : Real.log c ≤ 0 := Real.log_nonpos hc.le hc1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 ≤ 1 + (a + b - Real.log c) / Real.log 2 := by
    have hnum : 0 ≤ a + b - Real.log c := by linarith
    positivity
  filter_upwards [PolynomialLogEnvelope.eventually_bound
    (1 + (a + b - Real.log c) / Real.log 2) 1 δ hC hδ] with X hX
  refine ⟨hX.1, ?_⟩
  intro v U hv hU
  exact (logarithmic_bound_of_powers v U X c a b hX.1 hc hc1 ha hb hv hU).trans
    (by simpa only [pow_one] using hX.2)

end BandCountEnvelope

#print axioms BandCountEnvelope.eventually_bound_of_powers
run_cmd do
  for target in [``BandCountEnvelope.logarithmic_bound_of_powers,
      ``BandCountEnvelope.eventually_bound_of_powers] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "POWER BAND COUNT ENVELOPE PASSED"
