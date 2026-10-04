import FiniteMellinInversion
import MellinWindowWeight

/-!
Integrability on every positive real coordinate, extending the existing
finite inversion helper from sigma>1 to sigma>0. The auxiliary Perron
coordinate will be 1/ell while the zeta coordinate is 1+1/ell.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set

namespace SmoothMellinVertical
open MellinWindowFactor

theorem continuous (ν : ℝ → ℝ) (epsilon sigma : ℝ)
    (hν : ContDiff ℝ 1 ν) (hnonneg : ∀ x > 0, 0 ≤ ν x)
    (hsupport : Function.support ν ⊆ Icc (1 / 2) 2)
    (hmass : ∫ x in Ioi 0, ν x / x = 1)
    (hepsilon : epsilon ∈ Ioo 0 1) (hsigma : 0 < sigma) :
    Continuous (fun t : ℝ =>
      mellin (fun x => (Smooth1 ν epsilon x : ℂ)) (line sigma t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hh := (Smooth1MellinDifferentiable hν hsupport hepsilon hnonneg hmass
    (s := line sigma t) (by simpa [line] using hsigma)).continuousAt
  exact hh.comp (by unfold line; fun_prop)

theorem integrable (ν : ℝ → ℝ) (epsilon sigma : ℝ)
    (hν : ContDiff ℝ 1 ν) (hnonneg : ∀ x > 0, 0 ≤ ν x)
    (hsupport : Function.support ν ⊆ Icc (1 / 2) 2)
    (hmass : ∫ x in Ioi 0, ν x / x = 1)
    (hepsilon : epsilon ∈ Ioo 0 1) (hsigma : 0 < sigma) (hsigma2 : sigma ≤ 2) :
    Integrable (fun t : ℝ =>
      mellin (fun x => (Smooth1 ν epsilon x : ℂ)) (line sigma t)) := by
  obtain ⟨C, hC, hdecay⟩ := MellinOfSmooth1b hν hsupport
  have hbase : Integrable (fun t : ℝ => (‖line sigma t‖ ^ 2)⁻¹) := by
    simpa only [line, mul_comm Complex.I] using
      poisson_kernel_integrable sigma hsigma.ne'
  apply Integrable.mono' (hbase.const_mul (C / epsilon))
    (continuous ν epsilon sigma hν hnonneg hsupport hmass hepsilon hsigma).aestronglyMeasurable
  filter_upwards with t
  have hh := hdecay (sigma / 2) (by linarith) (line sigma t)
    (by simpa [line] using (show sigma / 2 ≤ sigma by linarith))
    (by simpa [line] using hsigma2) epsilon hepsilon.1 hepsilon.2
  apply hh.trans_eq
  rw [mul_inv_rev]
  ring

theorem decay (ν : ℝ → ℝ) (hν : ContDiff ℝ 1 ν)
    (hsupport : Function.support ν ⊆ Icc (1 / 2) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ epsilon sigma t : ℝ,
      epsilon ∈ Ioo 0 1 → 0 < sigma → sigma ≤ 2 → t ≠ 0 →
      ‖mellin (fun x => (Smooth1 ν epsilon x : ℂ)) (line sigma t)‖ ≤
        C / (epsilon * t ^ 2) := by
  obtain ⟨C, hC, hdecay⟩ := MellinOfSmooth1b hν hsupport
  refine ⟨C, hC, ?_⟩
  intro epsilon sigma t hepsilon hsigma hsigma2 ht
  have hh := hdecay (sigma / 2) (by linarith) (line sigma t)
    (by simpa [line] using (show sigma / 2 ≤ sigma by linarith))
    (by simpa [line] using hsigma2) epsilon hepsilon.1 hepsilon.2
  apply hh.trans
  rw [← div_eq_mul_inv, MellinWindowWeight.norm_line_square]
  apply div_le_div_of_nonneg_left hC.le
    (mul_pos hepsilon.1 (sq_pos_of_ne_zero ht))
  exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg sigma]) hepsilon.1.le

theorem finite_sum (s : Finset ℕ) (coeff : ℕ → ℂ) (ν : ℝ → ℝ)
    (X sigma epsilon : ℝ) (hX : 0 < X) (hs : ∀ n ∈ s, 0 < n)
    (hsigma : 0 < sigma) (hsigma2 : sigma ≤ 2) (hepsilon : epsilon ∈ Ioo 0 1)
    (hν : ContDiff ℝ 1 ν) (hnonneg : ∀ x > 0, 0 ≤ ν x)
    (hsupport : Function.support ν ⊆ Icc (1 / 2) 2)
    (hmass : ∫ x in Ioi 0, ν x / x = 1) :
    (∑ n ∈ s, coeff n * (Smooth1 ν epsilon ((n : ℝ) / X) : ℂ)) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, Erdos374.HarmanGram152.verticalDirichlet152 s coeff sigma t *
          mellin (fun x => (Smooth1 ν epsilon x : ℂ)) (line sigma t) *
            (X : ℂ) ^ line sigma t := by
  apply FiniteMellinInversion.finite_sum s coeff
    (fun x => (Smooth1 ν epsilon x : ℂ)) X sigma hX hs
  · exact Smooth1MellinConvergent hν hsupport hepsilon hnonneg hmass
      (by simpa only [Complex.ofReal_re] using hsigma)
  · simpa only [Complex.VerticalIntegrable, line, mul_comm Complex.I] using
      integrable ν epsilon sigma hν hnonneg hsupport hmass hepsilon hsigma hsigma2
  · intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hs n hn
    exact Complex.continuous_ofReal.continuousAt.comp
      (Smooth1ContinuousAt hν hnonneg hsupport hepsilon.1 (div_pos hnpos hX))

end SmoothMellinVertical

#print axioms SmoothMellinVertical.finite_sum
run_cmd do
  for target in [``SmoothMellinVertical.continuous,
      ``SmoothMellinVertical.integrable, ``SmoothMellinVertical.decay,
      ``SmoothMellinVertical.finite_sum] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "SMOOTH MELLIN VERTICAL PASSED"
