import FlatCofactorApproximation
import SmoothedWindowNorm
import SmoothedDirichletKernel

/-!
The first-order cofactor approximation inside the actual low-frequency
smoothed contour. A fourth-root cutoff makes its error power-saving.
The continuous cofactor contour is not yet evaluated here.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set

namespace FlatCofactorContour
open Erdos374.HarmanGram152 SmoothedWindowTransfer SmoothedDirichletKernel
open MellinWindowFactor

def continuousPolynomial (lo hi : ℕ) (σ t : ℝ) : ℂ :=
  ((hi : ℂ) ^ (1 - line σ t) - (lo : ℂ) ^ (1 - line σ t)) /
    (1 - line σ t)

theorem continuous_polynomial (lo hi : ℕ) (σ : ℝ)
    (hlo : 0 < lo) (hhi : 0 < hi) (hσ : 1 < σ) :
    Continuous (continuousPolynomial lo hi σ) := by
  have hline : Continuous (fun t => (1 : ℂ) - line σ t) := by
    unfold line
    fun_prop
  unfold continuousPolynomial
  apply Continuous.div
  · exact (hline.const_cpow (Or.inl (by exact_mod_cast Nat.ne_of_gt hhi))).sub
      (hline.const_cpow (Or.inl (by exact_mod_cast Nat.ne_of_gt hlo)))
  · exact hline
  · intro t heq
    have hh := congrArg Complex.re heq
    simp [line] at hh
    linarith

theorem bound (K lo hi : ℕ) (s : Finset ℕ) (coeff : ℕ → ℂ)
    (ε σ δ x H : ℝ) (hK : 1 ≤ K) (hlo : K ≤ lo)
    (hhi : lo < hi) (hs : ∀ n ∈ s, 0 < n)
    (hε : ε ∈ Ioo 0 1) (hσ : 1 < σ) (hσtwo : σ ≤ 2)
    (hx : 0 < x) (hδ : 0 ≤ δ) (hδone : δ < 1) (hH : 0 ≤ H) :
    ‖transform
        (fun t => verticalDirichlet152 s coeff σ t *
          verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t)
        MellinSmoothingFunction.smoothing ε (-H) H σ δ x -
      transform
        (fun t => verticalDirichlet152 s coeff σ t * continuousPolynomial lo hi σ t)
        MellinSmoothingFunction.smoothing ε (-H) H σ δ x‖ ≤
      8 * coefficientMass s coeff σ * δ * x ^ σ * H * (3 + H) / K := by
  have hA := NormalizedMeanSquare.continuous_vertical s coeff σ hs
  have hflat : Continuous
      (verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ) := by
    apply NormalizedMeanSquare.continuous_vertical
    intro n hn
    have hh := (Finset.mem_Ioc.mp hn).1
    omega
  have hC := continuous_polynomial lo hi σ (by omega) (by omega) hσ
  rw [SmoothedWindowNorm.transform_sub
    (fun t => verticalDirichlet152 s coeff σ t *
      verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t)
    (fun t => verticalDirichlet152 s coeff σ t * continuousPolynomial lo hi σ t)
    ε (-H) H σ δ x
    (hA.mul hflat) (hA.mul hC) hε (by linarith) hx hδone]
  apply (SmoothedWindowNorm.transform_bound _ ε (-H) H σ δ x
    (coefficientMass s coeff σ * ((3 + H) / K)) hε hσ.le hσtwo hx hδ hδone
    (by linarith) ?_).trans_eq
  · ring
  · intro t ht
    rw [← mul_sub, norm_mul]
    have htH : |t| ≤ H := abs_le.mpr ht
    have herror := FlatCofactorApproximation.bound_any_upper K lo hi σ t
      hK hlo hhi hσ hσtwo
    change ‖verticalDirichlet152 s coeff σ t‖ *
      ‖verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t -
        continuousPolynomial lo hi σ t‖ ≤ _
    apply mul_le_mul (polynomial_norm_le s coeff σ t hs) _
      (norm_nonneg _) (mass_nonnegative s coeff σ)
    exact herror.trans (div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg K))

theorem quarter_cutoff_bound (K lo hi : ℕ) (s : Finset ℕ) (coeff : ℕ → ℂ)
    (ε σ δ x H : ℝ) (hK : 1 ≤ K) (hlo : K ≤ lo)
    (hhi : lo < hi) (hs : ∀ n ∈ s, 0 < n)
    (hε : ε ∈ Ioo 0 1) (hσ : 1 < σ) (hσtwo : σ ≤ 2)
    (hx : 0 < x) (hδ : 0 ≤ δ) (hδone : δ < 1)
    (hH : 1 ≤ H) (hHK : H ≤ (K : ℝ) ^ (1 / 4 : ℝ)) :
    ‖transform
        (fun t => verticalDirichlet152 s coeff σ t *
          verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t)
        MellinSmoothingFunction.smoothing ε (-H) H σ δ x -
      transform
        (fun t => verticalDirichlet152 s coeff σ t * continuousPolynomial lo hi σ t)
        MellinSmoothingFunction.smoothing ε (-H) H σ δ x‖ ≤
      32 * coefficientMass s coeff σ * δ * x ^ σ * (K : ℝ) ^ (-1 / 2 : ℝ) := by
  have hKp : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hHp : 0 ≤ H := by linarith
  have hHsq : H ^ 2 ≤ (K : ℝ) ^ (1 / 2 : ℝ) := by
    have hh := pow_le_pow_left₀ hHp hHK 2
    rw [← Real.rpow_mul_natCast hKp.le] at hh
    norm_num at hh
    exact hh
  have hHprod : H * (3 + H) ≤ 4 * (K : ℝ) ^ (1 / 2 : ℝ) := by
    nlinarith
  have hmass := mass_nonnegative s coeff σ
  apply (bound K lo hi s coeff ε σ δ x H hK hlo hhi hs
    hε hσ hσtwo hx hδ hδone hHp).trans
  calc
    _ = (8 * coefficientMass s coeff σ * δ * x ^ σ) * (H * (3 + H)) / K := by ring
    _ ≤ (8 * coefficientMass s coeff σ * δ * x ^ σ) *
        (4 * (K : ℝ) ^ (1 / 2 : ℝ)) / K := by gcongr
    _ = 32 * coefficientMass s coeff σ * δ * x ^ σ *
        ((K : ℝ) ^ (1 / 2 : ℝ) / K) := by ring
    _ = _ := by
      have hid : (K : ℝ) ^ (1 / 2 : ℝ) / K = (K : ℝ) ^ (-1 / 2 : ℝ) := by
        calc
          _ = (K : ℝ) ^ (1 / 2 : ℝ) / (K : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_sub hKp]; norm_num
      rw [hid]

end FlatCofactorContour

#print axioms FlatCofactorContour.quarter_cutoff_bound
run_cmd do
  for target in [``FlatCofactorContour.continuous_polynomial,
      ``FlatCofactorContour.bound,
      ``FlatCofactorContour.quarter_cutoff_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "FLAT COFACTOR CONTOUR PASSED"
