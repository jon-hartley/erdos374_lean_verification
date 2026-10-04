import MellinSmoothingFunction

/-!
The smoothing multiplier costs a fixed factor on 0<sigma<=2, uniformly
in epsilon in (0,1). This allows the proved polynomial energy bound to
be used after smoothing without hiding an epsilon-dependent loss.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set

namespace SmoothMellinMultiplier
open MellinWindowFactor

def multiplier (Ψ : ℝ → ℝ) (ε σ t : ℝ) : ℂ :=
  line σ t * mellin (fun x => (Smooth1 Ψ ε x : ℂ)) (line σ t)

theorem raw_mellin_bound (Ψ : ℝ → ℝ) (z : ℂ) (hz : 0 ≤ z.re) (hztwo : z.re ≤ 2)
    (hnonneg : ∀ x > 0, 0 ≤ Ψ x)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ x in Ioi 0, Ψ x / x = 1) :
    ‖mellin (fun x => (Ψ x : ℂ)) z‖ ≤ 4 := by
  have hmajor : IntegrableOn (fun x => 4 * (Ψ x / x)) (Ioi 0) :=
    (integrable_of_integral_eq_one hmass).const_mul 4
  unfold mellin
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ x in Ioi 0, 4 * (Ψ x / x) := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxp : 0 < x := hx
      by_cases hzero : Ψ x = 0
      · simp [hzero]
      · have hs := hsupport hzero
        simp only [smul_eq_mul, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (hnonneg x hxp)]
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hxp]
        simp only [Complex.sub_re, Complex.one_re]
        rw [Real.rpow_sub hxp, Real.rpow_one]
        have hpow : x ^ z.re ≤ 4 := by
          calc
            _ ≤ (2 : ℝ) ^ z.re := Real.rpow_le_rpow hxp.le hs.2 hz
            _ ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hztwo
            _ = 4 := by norm_num
        calc
          x ^ z.re / x * Ψ x = (Ψ x / x) * x ^ z.re := by ring
          _ ≤ (Ψ x / x) * 4 := mul_le_mul_of_nonneg_left hpow
            (div_nonneg (hnonneg x hxp) hxp.le)
          _ = _ := by ring
    _ = 4 := by rw [integral_const_mul, hmass, mul_one]

theorem norm_le_four (Ψ : ℝ → ℝ) (ε σ t : ℝ) (hε : ε ∈ Ioo 0 1)
    (hσ : 0 < σ) (hσtwo : σ ≤ 2) (hdiff : ContDiff ℝ 1 Ψ)
    (hnonneg : ∀ x > 0, 0 ≤ Ψ x)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ x in Ioi 0, Ψ x / x = 1) :
    ‖multiplier Ψ ε σ t‖ ≤ 4 := by
  have hre : (line σ t).re = σ := by simp [line]
  unfold multiplier
  rw [MellinOfSmooth1a hdiff hsupport hε.1 (by rw [hre]; exact hσ),
    ← mul_assoc, mul_inv_cancel₀ (line_ne_zero σ t hσ), one_mul]
  apply raw_mellin_bound Ψ _ _ _ hnonneg hsupport hmass
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, hre]
    exact mul_nonneg hε.1.le hσ.le
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, hre]
    nlinarith [hε.1, hε.2]

theorem continuous_multiplier (Ψ : ℝ → ℝ) (ε σ : ℝ) (hε : ε ∈ Ioo 0 1)
    (hσ : 0 < σ) (hdiff : ContDiff ℝ 1 Ψ) (hnonneg : ∀ x > 0, 0 ≤ Ψ x)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ x in Ioi 0, Ψ x / x = 1) :
    Continuous (multiplier Ψ ε σ) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  unfold multiplier
  apply ContinuousAt.mul
  · unfold line
    fun_prop
  · have hh := (Smooth1MellinDifferentiable hdiff hsupport hε hnonneg hmass
        (s := line σ t) (by simpa [line] using hσ)).continuousAt
    exact hh.comp (by unfold line; fun_prop)

end SmoothMellinMultiplier

#print axioms SmoothMellinMultiplier.norm_le_four
run_cmd do
  for decl in [``SmoothMellinMultiplier.norm_le_four, ``SmoothMellinMultiplier.continuous_multiplier] do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "SMOOTH MELLIN MULTIPLIER PASSED"
