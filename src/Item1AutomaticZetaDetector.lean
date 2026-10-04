import Item1AutomaticZeroRemoval
import Item1ZetaDetectorDefinitions
import Item1EulerZeroDetector
import Item1ZeroDetectionScalar
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
The local detector now applies to the actual translated zeta function.
Root extraction, all multiplicities, the remaining-factor growth and the
zero-charge signs are constructed internally. The final theorem STILL requires
actual relative growth on the two original circles and the displayed real-axis
pole bound. It does not claim these quantitative bounds or the desired eventual
zero-free region have been proved by this module.
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000
noncomputable section
open Set Metric Complex Filter
open scoped BigOperators ComplexConjugate Topology
namespace Item1AutomaticZetaDetector
open Item1AutomaticZeroRemoval Item1EulerZeroDetector

theorem translated_ne_pole (σ t R : ℝ) (ht : R < t)
    (z : ℂ) (hz : z ∈ closedBall (0:ℂ) R) : center σ t+z ≠ 1 := by
  have hzR : ‖z‖ ≤ R := by simpa using hz
  have him : -R ≤ z.im := by
    have hi := (neg_le_abs z.im).trans (Complex.abs_im_le_norm z)
    linarith
  intro he
  have hh := congrArg Complex.im he
  simp [center] at hh
  linarith

theorem shifted_analytic (σ t R : ℝ) (ht : R < t) :
    AnalyticOnNhd ℂ (shifted σ t) (closedBall 0 R) := by
  intro z hz
  have hzeta : AnalyticAt ℂ riemannZeta (center σ t+z) :=
    analyticOn_riemannZeta _ (by simpa using translated_ne_pole σ t R ht z hz)
  exact hzeta.comp (analyticAt_const.add analyticAt_id)

theorem shifted_center_nonzero (σ t : ℝ) (hσ : 1 < σ) :
    shifted σ t 0 ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_lt_re
  simpa [center] using hσ

/-- Only ordinary open-right-half-plane nonvanishing is used to place the zeros. -/
theorem shifted_zero_left (σ t : ℝ) (hσ : 1 < σ) (z : ℂ)
    (hz : shifted σ t z = 0) : z.re ≤ 0 := by
  by_contra hn
  have hzpos : 0 < z.re := lt_of_not_ge hn
  have hr : 1 < (center σ t+z).re := by simp [center]; linarith
  exact (riemannZeta_ne_zero_of_one_lt_re hr) hz

theorem shifted_logDeriv_center (σ t : ℝ) (ht : 0 < t) :
    -(logDeriv (shifted σ t) 0).re = (F (center σ t)).re := by
  have hne : center σ t ≠ 1 := by
    intro he
    have hh := congrArg Complex.im he
    simp [center] at hh
    linarith
  have hd : HasDerivAt (fun z : ℂ => center σ t+z) 1 0 := by
    simpa using (hasDerivAt_id (0:ℂ)).const_add (center σ t)
  have hh := logDeriv_fun_comp
    (show DifferentiableAt ℂ riemannZeta (center σ t+0) by
      simpa using differentiableAt_riemannZeta hne) hd.differentiableAt
  change logDeriv (shifted σ t) 0 = _ at hh
  rw [hd.deriv, mul_one, add_zero] at hh
  rw [hh]
  simp only [F, logDeriv_apply, neg_div, Complex.neg_re]

theorem actual_disk_upper (σ t R M : ℝ)
    (hσ : 1 < σ) (hR : 0 < R) (hM : 0 < M) (ht : R < t)
    (hg : DiskGrowth σ t R M) :
    (F (center σ t)).re ≤ 4*M/R := by
  have hh := automatic_upper (shifted σ t) R M hR hM
    (shifted_analytic σ t R ht) (shifted_center_nonzero σ t hσ)
    hg (fun z _ hz => shifted_zero_left σ t hσ z hz)
  rwa [shifted_logDeriv_center σ t (hR.trans ht)] at hh

/-- The hypothetical zero is an actual zero of riemannZeta, not a supplied
root-list membership. Its membership and positive multiplicity are constructed. -/
theorem actual_disk_one_zero (σ β t R M : ℝ)
    (hσ : 1 < σ) (hR : 0 < R) (hM : 0 < M) (ht : R < t)
    (hq : 0 < σ-β) (hqR : σ-β < R)
    (hg : DiskGrowth σ t R M) (hz : riemannZeta (center β t) = 0) :
    (F (center σ t)).re ≤ 4*M/R - 1/(σ-β) + (σ-β)/R^2 := by
  have hz' : shifted σ t (-((σ-β:ℝ):ℂ)) = 0 := by
    have he : center σ t-((σ-β:ℝ):ℂ) = center β t := by
      unfold center
      push_cast
      ring
    simpa only [shifted, ←sub_eq_add_neg, he] using hz
  have hh := automatic_one_zero (shifted σ t) R M (σ-β) hR hM hq hqR
    (shifted_analytic σ t R ht) (shifted_center_nonzero σ t hσ)
    hg (fun z _ hzz => shifted_zero_left σ t hσ z hzz) hz'
  rwa [shifted_logDeriv_center σ t (hR.trans ht)] at hh

/-- A concrete local zeta exclusion theorem. No finite factorization, zero list,
logarithm branch, boundary nonvanishing, local derivative budget, or assumed
Euler positivity is a parameter. The original-circle growth and real-axis pole
inequality remain EXPLICIT quantitative hypotheses. -/
theorem local_zeta_exclusion (h R M t β : ℝ)
    (hh : 0 < h) (hR : 0 < R) (hM : 0 < M) (ht : R < t)
    (hr : 8*h ≤ R) (hbudget : 40*M*h/R ≤ 1/4)
    (hpole : (F ((1+h:ℝ):ℂ)).re ≤ 17/(16*h))
    (hg1 : DiskGrowth (1+h) t R M)
    (hg2 : DiskGrowth (1+h) (2*t) R M)
    (hb : 1-h/20 ≤ β) (hb1 : β ≤ 1) :
    riemannZeta (center β t) ≠ 0 := by
  intro hz
  have hσ : 1 < 1+h := by linarith
  have hdist := Item1ZeroDetectionScalar.candidate_distance h β hh hb hb1
  have hq : 0 < 1+h-β := hh.trans_le hdist.1
  have hqR : 1+h-β < R := by linarith [hdist.2]
  have h1 := actual_disk_one_zero (1+h) β t R M hσ hR hM ht hq hqR hg1 hz
  have h2 := actual_disk_upper (1+h) (2*t) R M hσ hR hM (by linarith) hg2
  have hMR : 4*M/R ≤ 8*M/R :=
    div_le_div_of_nonneg_right (by linarith) hR.le
  have hqRR : (1+h-β)/R^2 ≤ 4*(1+h-β)/R^2 :=
    div_le_div_of_nonneg_right (by linarith) (sq_nonneg R)
  have h1weak : (F (center (1+h) t)).re ≤
      8*M/R-1/(1+h-β)+4*(1+h-β)/R^2 :=
    h1.trans (add_le_add (sub_le_sub_right hMR _) hqRR)
  have h2weak : (F (center (1+h) (2*t))).re ≤ 8*M/R := h2.trans hMR
  have hpos := three_mode_nonneg (1+h) t hσ
  change 0 ≤ 3*(F ((1+h:ℝ):ℂ)).re + 4*(F (center (1+h) t)).re +
    (F (center (1+h) (2*t))).re at hpos
  exact Item1ZeroDetectionScalar.local_detector_contradiction h (1+h-β) R M
    (F ((1+h:ℝ):ℂ)).re (F (center (1+h) t)).re (F (center (1+h) (2*t))).re
    hh hR hdist.1 hdist.2 hr hbudget hpole h1weak h2weak hpos

/-- Euler handles beta > 1; the detector deals with the remaining interval. -/
theorem local_zeta_exclusion_all_right (h R M t β : ℝ)
    (hh : 0 < h) (hR : 0 < R) (hM : 0 < M) (ht : R < t)
    (hr : 8*h ≤ R) (hbudget : 40*M*h/R ≤ 1/4)
    (hpole : (F ((1+h:ℝ):ℂ)).re ≤ 17/(16*h))
    (hg1 : DiskGrowth (1+h) t R M)
    (hg2 : DiskGrowth (1+h) (2*t) R M)
    (hb : 1-h/20 ≤ β) : riemannZeta (center β t) ≠ 0 := by
  by_cases hb1 : β ≤ 1
  · exact local_zeta_exclusion h R M t β hh hR hM ht hr hbudget hpole hg1 hg2 hb hb1
  · apply riemannZeta_ne_zero_of_one_lt_re
    simpa [center] using lt_of_not_ge hb1

end Item1AutomaticZetaDetector

run_cmd do
  for target in [``Item1AutomaticZetaDetector.translated_ne_pole,
    ``Item1AutomaticZetaDetector.shifted_analytic,
    ``Item1AutomaticZetaDetector.shifted_center_nonzero,
    ``Item1AutomaticZetaDetector.shifted_zero_left,
    ``Item1AutomaticZetaDetector.shifted_logDeriv_center,
    ``Item1AutomaticZetaDetector.actual_disk_upper,
    ``Item1AutomaticZetaDetector.actual_disk_one_zero,
    ``Item1AutomaticZetaDetector.local_zeta_exclusion,
    ``Item1AutomaticZetaDetector.local_zeta_exclusion_all_right] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Item1AutomaticZetaDetector.local_zeta_exclusion_all_right
