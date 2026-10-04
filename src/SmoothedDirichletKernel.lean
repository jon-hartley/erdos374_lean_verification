import SmoothMellinMultiplier
import MellinWindowWeight
import IntegralTail

/-!
Absolute integrability and a quantitative truncation error for the
finite smoothed counting integral. The coefficient mass, epsilon loss,
spatial scale and truncation height all remain visible.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace SmoothedDirichletKernel
open MellinWindowFactor Erdos374.HarmanGram152

def coefficientMass (s : Finset ℕ) (coeff : ℕ → ℂ) (σ : ℝ) : ℝ :=
  ∑ n ∈ s, ‖coeff n‖ * (n : ℝ) ^ (-σ)

def integrand (s : Finset ℕ) (coeff : ℕ → ℂ) (Ψ : ℝ → ℝ) (ε X σ t : ℝ) : ℂ :=
  verticalDirichlet152 s coeff σ t *
    mellin (fun x => (Smooth1 Ψ ε x : ℂ)) (line σ t) * (X : ℂ) ^ line σ t

theorem mass_nonnegative (s : Finset ℕ) (coeff : ℕ → ℂ) (σ : ℝ) :
    0 ≤ coefficientMass s coeff σ := by
  unfold coefficientMass
  positivity

theorem polynomial_norm_le (s : Finset ℕ) (coeff : ℕ → ℂ) (σ t : ℝ)
    (hs : ∀ n ∈ s, 0 < n) :
    ‖verticalDirichlet152 s coeff σ t‖ ≤ coefficientMass s coeff σ := by
  unfold verticalDirichlet152 coefficientMass
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hs n hn
  rw [norm_mul]
  congr 1
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
  simp

theorem integrable_integrand (s : Finset ℕ) (coeff : ℕ → ℂ) (Ψ : ℝ → ℝ)
    (ε X σ : ℝ) (hX : 0 < X) (hs : ∀ n ∈ s, 0 < n)
    (hσ : 1 < σ) (hσtwo : σ ≤ 2) (hε : ε ∈ Ioo 0 1)
    (hdiff : ContDiff ℝ 1 Ψ) (hnonneg : ∀ x > 0, 0 ≤ Ψ x)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ x in Ioi 0, Ψ x / x = 1) :
    Integrable (integrand s coeff Ψ ε X σ) := by
  let f := fun x => (Smooth1 Ψ ε x : ℂ)
  have hv : Complex.VerticalIntegrable (mellin f) σ :=
    SmoothedChebyshevDirichlet_aux_integrable hdiff hnonneg hsupport hmass hε.1 hε.2 hσ hσtwo
  have hi : Integrable (fun t : ℝ => ∑ n ∈ s,
      coeff n * (((n : ℝ) / X : ℝ) : ℂ) ^ (-line σ t) * mellin f (line σ t)) := by
    apply integrable_finsetSum
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hs n hn
    simpa only [mul_assoc] using
      (FiniteMellinInversion.integrable_inverse_kernel f σ ((n : ℝ) / X)
        (div_pos hnpos hX) hv).const_mul (coeff n)
  apply hi.congr
  filter_upwards with t
  unfold integrand verticalDirichlet152
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [FiniteMellinInversion.ratio_power n X (by exact_mod_cast hs n hn) hX]
  unfold line
  push_cast
  dsimp [f]
  ring

theorem truncation_bound (Ψ : ℝ → ℝ) (hdiff : ContDiff ℝ 1 Ψ)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hnonneg : ∀ x > 0, 0 ≤ Ψ x) (hmass : ∫ x in Ioi 0, Ψ x / x = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset ℕ) (coeff : ℕ → ℂ) (ε X σ T : ℝ),
      0 < X → (∀ n ∈ s, 0 < n) → 1 < σ → σ ≤ 2 → ε ∈ Ioo 0 1 → 0 < T →
      ‖(∫ t : ℝ, integrand s coeff Ψ ε X σ t) -
        ∫ t in Icc (-T) T, integrand s coeff Ψ ε X σ t‖ ≤
          2 * (coefficientMass s coeff σ * C * X ^ σ / ε) / T := by
  obtain ⟨C, hC, hdecay⟩ := MellinOfSmooth1b hdiff hsupport
  refine ⟨C, hC, ?_⟩
  intro s coeff ε X σ T hX hs hσ hσtwo hε hT
  apply IntegralTail.symmetric_truncation _ _ _ hT
    (integrable_integrand s coeff Ψ ε X σ hX hs hσ hσtwo hε hdiff hnonneg hsupport hmass)
  intro t ht
  have htzero : t ≠ 0 := by intro hz; simp [hz] at ht; linarith
  have hsq : 0 < t ^ 2 := sq_pos_of_ne_zero htzero
  have hline : (line σ t).re = σ := by simp [line]
  have hmellin := hdecay 1 (by norm_num) (line σ t)
    (by rw [hline]; linarith) (by rw [hline]; exact hσtwo) ε hε.1 hε.2
  have hnorm : ‖mellin (fun x => (Smooth1 Ψ ε x : ℂ)) (line σ t)‖ ≤ C / (ε * t ^ 2) := by
    apply hmellin.trans
    rw [MellinWindowWeight.norm_line_square, ← div_eq_mul_inv]
    apply div_le_div_of_nonneg_left hC.le (mul_pos hε.1 hsq)
    exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg σ]) hε.1.le
  unfold integrand
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX, hline]
  calc
    _ ≤ coefficientMass s coeff σ * (C / (ε * t ^ 2)) * X ^ σ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (polynomial_norm_le s coeff σ t hs) hnorm
          (norm_nonneg _) (mass_nonnegative s coeff σ)) (Real.rpow_nonneg hX.le σ)
    _ = _ := by ring

end SmoothedDirichletKernel

#print axioms SmoothedDirichletKernel.truncation_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``SmoothedDirichletKernel.truncation_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "SMOOTHED DIRICHLET KERNEL PASSED"
