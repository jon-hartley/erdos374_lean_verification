import HarmanMellinTransfer

/-!
Exact Mellin factor for the interval (x-x*delta,x]. Its norm is bounded
both by delta and by 2/|t| on a vertical line with sigma >= 1.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Set

namespace MellinWindowFactor

def line (σ t : ℝ) : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)

def factor (σ δ t : ℝ) : ℂ :=
  (1 - ((1 - δ : ℝ) : ℂ) ^ line σ t) / line σ t

theorem line_ne_zero (σ t : ℝ) (hσ : 0 < σ) : line σ t ≠ 0 := by
  intro h
  have hh := congrArg Complex.re h
  simp [line] at hh
  linarith

theorem continuous_factor (σ δ : ℝ) (hσ : 0 < σ) (hδ : δ < 1) :
    Continuous (factor σ δ) := by
  have hbase : ((1 - δ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  unfold factor
  apply Continuous.div
  · apply continuous_const.sub
    exact (show Continuous (line σ) by unfold line; fun_prop).const_cpow (Or.inl hbase)
  · unfold line
    fun_prop
  · exact fun t => line_ne_zero σ t hσ

theorem integral_representation (σ δ t : ℝ) (hσ : 1 ≤ σ) :
    factor σ δ t = ∫ u : ℝ in (1 - δ)..1, (u : ℂ) ^ (line σ t - 1) := by
  rw [integral_cpow (Or.inl (show -1 < (line σ t - 1).re by
    simp only [line, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.one_re]
    linarith))]
  simp only [sub_add_cancel, Complex.ofReal_one, Complex.one_cpow]
  rfl

theorem norm_le_width (σ δ t : ℝ) (hσ : 1 ≤ σ) (hδ : 0 ≤ δ) (hδone : δ < 1) :
    ‖factor σ δ t‖ ≤ δ := by
  rw [integral_representation σ δ t hσ]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 1 - δ) (b := 1) (C := (1 : ℝ)) (f := fun u : ℝ => (u : ℂ) ^ (line σ t - 1)) (by
      intro u hu
      rw [uIoc_of_le (by linarith : 1 - δ ≤ (1 : ℝ))] at hu
      have hup : 0 < u := by linarith [hu.1]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hup]
      have hre : (line σ t - 1).re = σ - 1 := by simp [line]
      rw [hre]
      exact Real.rpow_le_one hup.le hu.2 (by linarith))
  simpa only [sub_sub_cancel, abs_of_nonneg hδ, one_mul] using hh

theorem norm_le_line (σ δ t : ℝ) (hσ : 1 ≤ σ)
    (hδ : 0 ≤ δ) (hδone : δ < 1) :
    ‖factor σ δ t‖ ≤ 2 / ‖line σ t‖ := by
  have hbase : 0 < 1 - δ := by linarith
  have hpower : ‖((1 - δ : ℝ) : ℂ) ^ line σ t‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hbase]
    simp only [line, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
    exact Real.rpow_le_one hbase.le (by linarith) (by linarith)
  have hnum : ‖1 - ((1 - δ : ℝ) : ℂ) ^ line σ t‖ ≤ 2 := by
    have hh := norm_sub_le (1 : ℂ) (((1 - δ : ℝ) : ℂ) ^ line σ t)
    simp only [norm_one] at hh
    linarith
  unfold factor
  rw [norm_div]
  exact div_le_div_of_nonneg_right hnum (norm_nonneg _)

theorem norm_le_frequency (σ δ t : ℝ) (hσ : 1 ≤ σ)
    (hδ : 0 ≤ δ) (hδone : δ < 1) (ht : t ≠ 0) :
    ‖factor σ δ t‖ ≤ 2 / |t| := by
  have him : |t| ≤ ‖line σ t‖ := by simpa [line] using Complex.abs_im_le_norm (line σ t)
  exact (norm_le_line σ δ t hσ hδ hδone).trans
    (div_le_div_of_nonneg_left (by norm_num) (abs_pos.mpr ht) him)

end MellinWindowFactor

#print axioms MellinWindowFactor.norm_le_width
run_cmd do
  for decl in [``MellinWindowFactor.continuous_factor, ``MellinWindowFactor.integral_representation,
      ``MellinWindowFactor.norm_le_width, ``MellinWindowFactor.norm_le_line,
      ``MellinWindowFactor.norm_le_frequency] do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "MELLIN WINDOW FACTOR PASSED"
