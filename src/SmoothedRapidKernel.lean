import SmoothedDirichletKernel
import MellinRapidDecay
import PowerIntegralTail

/-!
Arbitrary fixed-order frequency truncation for the smoothed finite
Dirichlet integral. The gain is a power of epsilon*T; the constants are
chosen before epsilon, the coefficients, the scale and truncation height.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace SmoothedRapidKernel
open SmoothedDirichletKernel MellinWindowFactor

theorem truncation_bound (k : ℕ) (Ψ : ℝ → ℝ) (hdiff : ContDiff ℝ ∞ Ψ)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hnonneg : ∀ x > 0, 0 ≤ Ψ x) (hmass : ∫ x in Ioi 0, Ψ x / x = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset ℕ) (coeff : ℕ → ℂ) (ε X σ T : ℝ),
      0 < X → (∀ n ∈ s, 0 < n) → 1 < σ → σ ≤ 2 → ε ∈ Ioo 0 1 → 0 < T →
      ‖(∫ t : ℝ, integrand s coeff Ψ ε X σ t) -
        ∫ t in Icc (-T) T, integrand s coeff Ψ ε X σ t‖ ≤
          2 * coefficientMass s coeff σ * C * X ^ σ /
            (((k + 1 : ℕ) : ℝ) * (ε * T) ^ (k + 1)) := by
  obtain ⟨C, hC, hdecay⟩ := MellinRapidDecay.smooth_decay k Ψ hdiff hsupport
  refine ⟨C, hC, ?_⟩
  intro s coeff ε X σ T hX hs hσ hσtwo hε hT
  let A := coefficientMass s coeff σ * C * X ^ σ / ε ^ (k + 1)
  have htail := PowerIntegralTail.symmetric_truncation (integrand s coeff Ψ ε X σ)
    A T ((k : ℝ) + 2) hT (by have hh := Nat.cast_nonneg (α := ℝ) k; linarith)
    (integrable_integrand s coeff Ψ ε X σ hX hs hσ hσtwo hε
      (hdiff.of_le (by simp)) hnonneg hsupport hmass) (by
      intro t ht
      have htpos : 0 < |t| := hT.trans ht
      have hline : (line σ t).re = σ := by simp [line]
      have hnorm := hdecay ε (line σ t) hε (by rw [hline]; linarith)
        (by rw [hline]; exact hσtwo)
      have hlow : |t| ≤ ‖line σ t‖ := by
        simpa [line] using Complex.abs_im_le_norm (line σ t)
      have hdec : ‖mellin (fun x => (Smooth1 Ψ ε x : ℂ)) (line σ t)‖ ≤
          C / (ε ^ (k + 1) * |t| ^ (k + 2)) := by
        apply hnorm.trans
        apply div_le_div_of_nonneg_left hC.le (mul_pos (pow_pos hε.1 _) (pow_pos htpos _))
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hlow (k + 2))
          (pow_nonneg hε.1.le _)
      unfold integrand
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX, hline]
      calc
        _ ≤ coefficientMass s coeff σ * (C / (ε ^ (k + 1) * |t| ^ (k + 2))) * X ^ σ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (polynomial_norm_le s coeff σ t hs) hdec
              (norm_nonneg _) (mass_nonnegative s coeff σ)) (Real.rpow_nonneg hX.le σ)
        _ = A * |t| ^ (-((k : ℝ) + 2)) := by
          rw [show (k : ℝ) + 2 = ((k + 2 : ℕ) : ℝ) by push_cast; ring,
            Real.rpow_neg_natCast]
          simp only [zpow_neg, zpow_natCast]
          dsimp [A]
          ring)
  apply htail.trans_eq
  rw [show 1 - ((k : ℝ) + 2) = -((k + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_neg_natCast,
    show (k : ℝ) + 2 - 1 = ((k + 1 : ℕ) : ℝ) by push_cast; ring]
  simp only [zpow_neg, zpow_natCast]
  dsimp [A]
  rw [mul_pow]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end SmoothedRapidKernel

#print axioms SmoothedRapidKernel.truncation_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``SmoothedRapidKernel.truncation_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "SMOOTHED RAPID KERNEL PASSED"
