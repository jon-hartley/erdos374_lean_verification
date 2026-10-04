import SmoothMellinMultiplier

/-!
Repeated integration by parts gives every fixed inverse power of the
Mellin frequency for a smooth compactly supported function. The constants
depend on the function and derivative order, but not on the frequency.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace MellinRapidDecay

def weightedDerivative (ν : ℝ → ℝ) (x : ℝ) : ℝ := x * deriv ν x

theorem derivative_smooth (ν : ℝ → ℝ) (hν : ContDiff ℝ ∞ ν) :
    ContDiff ℝ ∞ (weightedDerivative ν) :=
  contDiff_id.mul (contDiff_infty_iff_deriv.mp hν).2

theorem derivative_support (ν : ℝ → ℝ)
    (hν : Function.support ν ⊆ Icc (1 / 2) 2) :
    Function.support (weightedDerivative ν) ⊆ Icc (1 / 2) 2 := by
  intro x hx
  apply Function.support_deriv_subset_Icc hν
  intro hz
  exact hx (by simp [weightedDerivative, hz])

theorem integration_by_parts (ν : ℝ → ℝ) (hν : ContDiff ℝ 1 ν)
    (hsupport : Function.support ν ⊆ Icc (1 / 2) 2) (z : ℂ) (hz : z ≠ 0) :
    mellin (fun x => (ν x : ℂ)) z =
      -(1 / z) * mellin (fun x => (weightedDerivative ν x : ℂ)) z := by
  unfold mellin
  simp only [smul_eq_mul]
  calc
    _ = ∫ x in Ioi 0, (ν x : ℂ) * (x : ℂ) ^ (z - 1) := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = -(1 / z) * ∫ x : ℝ in Ioi 0, ((deriv ν x : ℝ) : ℂ) * (x : ℂ) ^ z :=
      MellinOfPsi_aux hν hsupport hz
    _ = _ := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hxp : 0 < x := hx
      have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxp.ne'
      have hpower : (x : ℂ) ^ (z - 1) * (x : ℂ) = (x : ℂ) ^ z := by
        calc
          _ = (x : ℂ) ^ (z - 1) * (x : ℂ) ^ (1 : ℂ) := by rw [Complex.cpow_one]
          _ = (x : ℂ) ^ ((z - 1) + 1) := (Complex.cpow_add _ _ hxC).symm
          _ = _ := by rw [sub_add_cancel]
      unfold weightedDerivative
      push_cast
      rw [← hpower]
      ring

theorem raw_decay (k : ℕ) (ν : ℝ → ℝ) (hν : ContDiff ℝ ∞ ν)
    (hsupport : Function.support ν ⊆ Icc (1 / 2) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 0 < z.re → z.re ≤ 2 →
      ‖mellin (fun x => (ν x : ℂ)) z‖ ≤ C / ‖z‖ ^ (k + 1) := by
  induction k generalizing ν with
  | zero =>
      obtain ⟨C, hC, hbound⟩ := MellinOfPsi (hν.of_le (by simp)) hsupport
      refine ⟨C, hC, ?_⟩
      intro z hz hztwo
      simpa only [zero_add, pow_one, div_eq_mul_inv] using hbound z.re hz z le_rfl hztwo
  | succ k ih =>
      obtain ⟨C, hC, hbound⟩ := ih (weightedDerivative ν) (derivative_smooth ν hν)
        (derivative_support ν hsupport)
      refine ⟨C, hC, ?_⟩
      intro z hz hztwo
      have hz0 : z ≠ 0 := by intro he; simp [he] at hz
      rw [integration_by_parts ν (hν.of_le (by simp)) hsupport z hz0,
        norm_mul, norm_neg, norm_div, norm_one]
      calc
        _ ≤ (1 / ‖z‖) * (C / ‖z‖ ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left (hbound z hz hztwo) (by positivity)
        _ = _ := by rw [pow_succ]; ring

theorem smooth_decay (k : ℕ) (ν : ℝ → ℝ) (hν : ContDiff ℝ ∞ ν)
    (hsupport : Function.support ν ⊆ Icc (1 / 2) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (z : ℂ), ε ∈ Ioo 0 1 → 0 < z.re → z.re ≤ 2 →
      ‖mellin (fun x => (Smooth1 ν ε x : ℂ)) z‖ ≤
        C / (ε ^ (k + 1) * ‖z‖ ^ (k + 2)) := by
  obtain ⟨C, hC, hbound⟩ := raw_decay k ν hν hsupport
  refine ⟨C, hC, ?_⟩
  intro ε z hε hz hztwo
  have hproductpos : 0 < ((ε : ℂ) * z).re := by
    simpa using mul_pos hε.1 hz
  have hproducttwo : ((ε : ℂ) * z).re ≤ 2 := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith [hε.1, hε.2]
  rw [MellinOfSmooth1a (hν.of_le (by simp)) hsupport hε.1 hz, norm_mul, norm_inv]
  calc
    _ ≤ ‖z‖⁻¹ * (C / ‖(ε : ℂ) * z‖ ^ (k + 1)) :=
      mul_le_mul_of_nonneg_left (hbound _ hproductpos hproducttwo) (by positivity)
    _ = _ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε.1, mul_pow,
        show k + 2 = (k + 1) + 1 by omega, pow_succ]
      ring

theorem smoothing_smooth : ContDiff ℝ ∞ MellinSmoothingFunction.smoothing :=
  contDiff_id.mul (MellinSmoothingFunction.bump.contDiff.div_const _)

end MellinRapidDecay

#print axioms MellinRapidDecay.smooth_decay
run_cmd do
  for decl in [``MellinRapidDecay.smooth_decay, ``MellinRapidDecay.smoothing_smooth] do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "MELLIN RAPID DECAY PASSED"
