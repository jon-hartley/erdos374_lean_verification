import TailRemainderBand

/-! A direct squared-mean to absolute-mean adapter on the physical window.
The pointwise Young inequality avoids any sign or cancellation assumption. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set

namespace TripleFirstMean

theorem absolute_mean_le (f : ℝ → ℝ) (X B : ℝ) (hX : 0 < X) (hB : 0 < B)
    (hf : IntegrableOn f (Icc X (2*X)))
    (hf2 : IntegrableOn (fun x => f x ^ 2) (Icc X (2*X)))
    (hsq : (1/X) * (∫ x in Icc X (2*X), f x ^ 2) ≤ B^2) :
    (1/X) * (∫ x in Icc X (2*X), |f x|) ≤ B := by
  have hc : IntegrableOn (fun _ : ℝ => B^2) (Icc X (2*X)) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hh := setIntegral_mono_on (hf.abs.const_mul (2*B)) (hf2.add hc)
    measurableSet_Icc (fun x (_hx : x ∈ Icc X (2*X)) => by
      dsimp
      nlinarith [sq_nonneg (|f x|-B), sq_abs (f x)])
  simp only [Pi.add_apply] at hh
  rw [integral_const_mul, integral_add hf2 hc, setIntegral_const,
    Real.volume_real_Icc_of_le (by linarith : X ≤ 2*X), smul_eq_mul] at hh
  have hs : (∫ x in Icc X (2*X), f x ^ 2) / X ≤ B^2 := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using hsq
  have hi := (div_le_iff₀ hX).mp hs
  rw [one_div, mul_comm, ← div_eq_mul_inv]
  apply (div_le_iff₀ hX).mpr
  nlinarith

theorem remainder_absolute_mean_le (S : Finset ℕ) (w : ℕ → ℝ) (X Y B : ℝ)
    (hX : 0 < X) (hY : 0 ≤ Y) (hYX : Y ≤ X) (hB : 0 < B)
    (hsq : (1/X) * (∫ x in Icc X (2*X),
      HarmanDivisorWindow.remainder S w (x-x*(Y/X)) x ^ 2) ≤ B^2) :
    (1/X) * (∫ x in Icc X (2*X),
      |HarmanDivisorWindow.remainder S w (x-x*(Y/X)) x|) ≤ B := by
  apply absolute_mean_le _ X B hX hB _ _ hsq
  · simpa only [mul_div_assoc] using TailRemainderBand.moving_remainder_integrable S w X Y
  · exact SignedDivisorRegularity.integrable_remainder_square S w X (Y/X) hX.le
      ⟨div_nonneg hY hX.le, (div_le_one hX).mpr hYX⟩

run_cmd do
  for decl in [``absolute_mean_le, ``remainder_absolute_mean_le] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "PHYSICAL ABSOLUTE FIRST MEAN FROM SQUARE MEAN PASSED"

end TripleFirstMean
