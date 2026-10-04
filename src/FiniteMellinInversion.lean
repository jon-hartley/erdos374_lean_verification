import MellinWindowFactor
import NormalizedMeanSquare

/-!
Finite weighted counting from Mellin inversion. The analytic hypotheses
are exposed in the general theorem and discharged for the seed's Smooth1
cutoff in the specialization. No prime-density conclusion is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace FiniteMellinInversion
open MellinWindowFactor Erdos374.HarmanGram152

theorem ratio_power (n X : ℝ) (hn : 0 < n) (hX : 0 < X) (z : ℂ) :
    ((n / X : ℝ) : ℂ) ^ (-z) = (n : ℂ) ^ (-z) * (X : ℂ) ^ z := by
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hn.le hX.le,
    Complex.cpow_neg, Complex.cpow_neg, div_inv_eq_mul]

theorem integrable_inverse_kernel (f : ℝ → ℂ) (σ r : ℝ) (hr : 0 < r)
    (hf : Complex.VerticalIntegrable (mellin f) σ) :
    Integrable (fun t : ℝ => (r : ℂ) ^ (-line σ t) * mellin f (line σ t)) := by
  have hvertical : Integrable (fun t : ℝ => mellin f (line σ t)) := by
    simpa only [Complex.VerticalIntegrable, line, mul_comm Complex.I] using hf
  have hcontinuous : Continuous (fun t : ℝ => (r : ℂ) ^ (-line σ t)) := by
    apply Continuous.const_cpow
    · unfold line
      fun_prop
    · exact Or.inl (Complex.ofReal_ne_zero.mpr hr.ne')
  apply hvertical.bdd_mul (c := r ^ (-σ)) hcontinuous.aestronglyMeasurable
  filter_upwards with t
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
  exact le_of_eq (by simp [line])

theorem finite_sum (s : Finset ℕ) (coeff : ℕ → ℂ) (f : ℝ → ℂ)
    (X σ : ℝ) (hX : 0 < X) (hs : ∀ n ∈ s, 0 < n)
    (hf : MellinConvergent f σ) (hvertical : Complex.VerticalIntegrable (mellin f) σ)
    (hcontinuous : ∀ n ∈ s, ContinuousAt f ((n : ℝ) / X)) :
    (∑ n ∈ s, coeff n * f ((n : ℝ) / X)) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, verticalDirichlet152 s coeff σ t *
          mellin f (line σ t) * (X : ℂ) ^ line σ t := by
  have hterm (n : ℕ) (hn : n ∈ s) :
      coeff n * f ((n : ℝ) / X) =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ, coeff n * (((n : ℝ) / X : ℝ) : ℂ) ^ (-line σ t) *
            mellin f (line σ t) := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hs n hn
    have hh := mellinInv_mellin_eq σ f (div_pos hnpos hX) hf hvertical (hcontinuous n hn)
    have hinv : f ((n : ℝ) / X) =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ, (((n : ℝ) / X : ℝ) : ℂ) ^ (-line σ t) *
            mellin f (line σ t) := by
      simpa only [mellinInv, Complex.real_smul, smul_eq_mul, line,
        mul_comm Complex.I] using hh.symm
    rw [hinv]
    simp_rw [mul_assoc, integral_const_mul]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards with t
    unfold verticalDirichlet152
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    rw [ratio_power n X (by exact_mod_cast hs n hn) hX]
    unfold line
    push_cast
    ring
  · intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hs n hn
    simpa only [mul_assoc] using
      (integrable_inverse_kernel f σ ((n : ℝ) / X) (div_pos hnpos hX) hvertical).const_mul (coeff n)

theorem smooth_finite_sum (s : Finset ℕ) (coeff : ℕ → ℂ) (Ψ : ℝ → ℝ)
    (X σ ε : ℝ) (hX : 0 < X) (hs : ∀ n ∈ s, 0 < n)
    (hσ : 1 < σ) (hσtwo : σ ≤ 2) (hε : ε ∈ Ioo 0 1)
    (hdiff : ContDiff ℝ 1 Ψ) (hnonneg : ∀ x > 0, 0 ≤ Ψ x)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ x in Ioi 0, Ψ x / x = 1) :
    (∑ n ∈ s, coeff n * (Smooth1 Ψ ε ((n : ℝ) / X) : ℂ)) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, verticalDirichlet152 s coeff σ t *
          mellin (fun x => (Smooth1 Ψ ε x : ℂ)) (line σ t) *
            (X : ℂ) ^ line σ t := by
  apply finite_sum s coeff (fun x => (Smooth1 Ψ ε x : ℂ)) X σ hX hs
  · exact Smooth1MellinConvergent hdiff hsupport hε hnonneg hmass
      (by simp only [Complex.ofReal_re]; linarith)
  · exact SmoothedChebyshevDirichlet_aux_integrable hdiff hnonneg hsupport hmass
      hε.1 hε.2 hσ hσtwo
  · intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hs n hn
    exact Complex.continuous_ofReal.continuousAt.comp
      (Smooth1ContinuousAt hdiff hnonneg hsupport hε.1 (div_pos hnpos hX))

end FiniteMellinInversion

#print axioms FiniteMellinInversion.smooth_finite_sum
run_cmd do
  for decl in [``FiniteMellinInversion.finite_sum, ``FiniteMellinInversion.smooth_finite_sum] do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "FINITE MELLIN INVERSION PASSED"
