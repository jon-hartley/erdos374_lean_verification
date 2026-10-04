import ContinuousCofactorTail
import FourfoldCofactorMainTerm
import SignedDivisorErrorDecomposition
import SmoothedFrequencySplit
import SpatialErrorBudget
import FourfoldCoefficientMass
import CofactorPowerError
import PolynomialLogEnvelope

/-! The fixed-cofactor, full-contour truncation error for the actual signed divisor count. -/

set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open Filter MeasureTheory Set

namespace FourfoldContinuousTruncation
open Erdos374.HarmanGram152 MellinWindowFactor MellinSmoothingFunction
open MellinCofactorCoverage ContinuousCofactorMellin ContinuousCofactorTail
open SmoothedDirichletKernel SignedDivisorErrorDecomposition

private theorem phase_eq (d e y v ε : ℝ)
    (hd : 0 < d) (he : 0 < e) (hy : 0 < y) (hv : 0 < v) :
    endpointPhase d e y v ε = Real.log (y * v ^ ε / (d * e)) := by
  have hq : 0 < v ^ ε := Real.rpow_pos_of_pos hv _
  unfold endpointPhase
  rw [Real.log_div (mul_pos hy hq).ne' (mul_pos hd he).ne',
    Real.log_mul hy.ne' hq.ne', Real.log_rpow hv,
    Real.log_mul hd.ne' he.ne']
  ring

private theorem phase_gaps (X A x δ ε : ℝ) (s : Finset ℕ)
    (hX : 0 < X) (hA : 0 < A)
    (hx : x ∈ Icc X (2 * X)) (hδ : δ ∈ Icc 0 (1 / 2))
    (hε : ε ∈ Ioo 0 (1 / 4))
    (hlo : 1 ≤ lowerCutoff X A)
    (hs : ∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A) :
    (∀ d ∈ s, ∀ y ∈ Icc (x - x * δ) x,
      ∀ v ∈ Icc (1 / 2 : ℝ) 2,
      Real.log 2 / 2 ≤
        |endpointPhase d (lowerCutoff X A) y v ε|) ∧
    (∀ d ∈ s, ∀ y ∈ Icc (x - x * δ) x,
      ∀ v ∈ Icc (1 / 2 : ℝ) 2,
      Real.log 2 / 2 ≤
        |endpointPhase d (upperCutoff X A) y v ε|) := by
  have hhi : 1 ≤ upperCutoff X A :=
    le_trans hlo (cutoff_strict X A hX hA).le
  have hw := DyadicDivisorWindow.window_bounds X x δ hX hx hδ
  have hleft : 0 < x - x * δ := by linarith [hw.1]
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hε' : ε ∈ Icc (0 : ℝ) (1 / 4) := ⟨hε.1.le, hε.2.le⟩
  constructor
  · intro d hd y hy v hv
    have hm := FourfoldDivisorCoverage.smoothed_phase_bounds X A x δ v ε y d
      hX hA (hs d hd) hx hδ hv hε' hy hlo hhi
    have hdp : (0 : ℝ) < d := hA.trans (hs d hd).1
    have hlop : (0 : ℝ) < lowerCutoff X A := by exact_mod_cast (by omega : 0 < lowerCutoff X A)
    have hyp : 0 < y := hleft.trans_le hy.1
    have hvp : 0 < v := by linarith [hv.1]
    rw [phase_eq d (lowerCutoff X A) y v ε hdp hlop hyp hvp]
    have habs := le_abs_self
      (Real.log (y * v ^ ε / ((d : ℝ) * lowerCutoff X A)))
    linarith [hm.1]
  · intro d hd y hy v hv
    have hm := FourfoldDivisorCoverage.smoothed_phase_bounds X A x δ v ε y d
      hX hA (hs d hd) hx hδ hv hε' hy hlo hhi
    have hdp : (0 : ℝ) < d := hA.trans (hs d hd).1
    have hhip : (0 : ℝ) < upperCutoff X A := by exact_mod_cast (by omega : 0 < upperCutoff X A)
    have hyp : 0 < y := hleft.trans_le hy.1
    have hvp : 0 < v := by linarith [hv.1]
    rw [phase_eq d (upperCutoff X A) y v ε hdp hhip hyp hvp]
    have habs := neg_le_abs
      (Real.log (y * v ^ ε / ((d : ℝ) * upperCutoff X A)))
    linarith [hm.2]

theorem truncation_bound (X A x δ ε σ H : ℝ)
    (s : Finset ℕ) (weight : ℕ → ℝ)
    (hX : 0 < X) (hA : 0 < A)
    (hx : x ∈ Icc X (2 * X)) (hδ : δ ∈ Icc 0 (1 / 2))
    (hε : ε ∈ Ioo 0 (1 / 4))
    (hσ : 1 < σ) (hσtwo : σ ≤ 2) (hH : 0 < H)
    (hlo : 1 ≤ lowerCutoff X A)
    (hs : ∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A) :
    ‖normalization * continuousBand s weight
        (lowerCutoff X A) (upperCutoff X A) ε (-H) H σ δ x -
      smoothedMain s weight ε δ x‖ ≤
      2 * ((x * δ) * (16 * x ^ (σ - 1) *
        ((lowerCutoff X A : ℝ) ^ (1 - σ) +
          (upperCutoff X A : ℝ) ^ (1 - σ))) *
          coefficientMass s (fun d => (weight d : ℂ)) σ /
            ((Real.log 2 / 2) * H)) := by
  let a : ℝ := lowerCutoff X A
  let b : ℝ := upperCutoff X A
  let coeff : ℕ → ℂ := fun d => (weight d : ℂ)
  let left : ℝ := x - x * δ
  let f : ℝ → ℂ := shortKernel s coeff smoothing ε σ left x a b
  have hxp : 0 < x := hX.trans_le hx.1
  have hw := DyadicDivisorWindow.window_bounds X x δ hX hx hδ
  have hleft : 0 < left := by dsimp [left]; linarith [hw.1]
  have hlex : left ≤ x := by dsimp [left]; nlinarith [hxp, hδ.1]
  have ha : 0 < a := by dsimp [a]; exact_mod_cast (by omega : 0 < lowerCutoff X A)
  have hab : a ≤ b := by
    dsimp [a, b]
    exact_mod_cast (cutoff_strict X A hX hA).le
  have hsp : ∀ d ∈ s, 0 < d := by
    intro d hd
    exact_mod_cast hA.trans (hs d hd).1
  have hεone : ε ∈ Ioo (0 : ℝ) 1 := ⟨hε.1, by linarith [hε.2]⟩
  have hg : 0 < Real.log 2 / 2 := by positivity
  have hgap := phase_gaps X A x δ ε s hX hA hx hδ hε hlo hs
  have hInt : Integrable f := short_kernel_integrable s coeff smoothing ε σ left x a b
    hleft hxp ha hab hsp hσ hσtwo hεone differentiable nonnegative
    support mass_one
  have hcof (t : ℝ) :
      FlatCofactorContour.continuousPolynomial (lowerCutoff X A)
        (upperCutoff X A) σ t = cofactor a b (line σ t) := by
    simpa [FlatCofactorContour.continuousPolynomial, a, b]
      using (cofactor_quotient a b σ t ha hab hσ).symm
  have hband : continuousBand s weight (lowerCutoff X A) (upperCutoff X A)
      ε (-H) H σ δ x = ∫ t in Icc (-H) H, f t := by
    unfold continuousBand SmoothedWindowTransfer.transform
    apply integral_congr_ae
    filter_upwards with t
    rw [hcof t]
    dsimp [f, shortKernel, coeff, left]
  have hfull : normalization * (∫ t : ℝ, f t) =
      smoothedMain s weight ε δ x := by
    have hm := FourfoldCofactorMainTerm.signed_contour_eq X A x δ ε σ s weight
      hX hA hx hδ hε hσ hσtwo hlo hs
    simpa only [CofactorMainTermBudget.coveredContour, normalization,
      f, shortKernel, coeff, left, a, b] using hm
  have hneg := negative_infinite_cofactor_tail s coeff smoothing ε σ left x a b H
    (Real.log 2 / 2) hleft hlex ha hab hsp hσ hσtwo hεone hH hg
    differentiable nonnegative support mass_one hgap.1 hgap.2
  have hpos := positive_infinite_cofactor_tail s coeff smoothing ε σ left x a b H
    (Real.log 2 / 2) hleft hlex ha hab hsp hσ hσtwo hεone hH hg
    differentiable nonnegative support mass_one hgap.1 hgap.2
  have hsplit := SmoothedFrequencySplit.whole_axis_error f H hH.le hInt
  rw [← hband] at hsplit
  rw [← hfull]
  have hdiff : ‖normalization * continuousBand s weight
      (lowerCutoff X A) (upperCutoff X A) ε (-H) H σ δ x -
      normalization * (∫ t : ℝ, f t)‖ ≤
        ‖(∫ t in Iic (-H), f t)‖ + ‖(∫ t in Ioi H, f t)‖ := by
    rw [← mul_sub]
    apply (SpatialErrorBudget.normalized_norm_le _).trans
    convert hsplit using 1
    rw [← norm_neg (continuousBand s weight (lowerCutoff X A)
      (upperCutoff X A) ε (-H) H σ δ x - ∫ t : ℝ, f t)]
    congr 1
    ring
  have hbound := hdiff.trans (add_le_add hneg hpos)
  dsimp [left, a, b, coeff] at hbound ⊢
  convert hbound using 1; ring

theorem truncation_bound_simple (X A x δ ε σ H : ℝ)
    (s : Finset ℕ) (weight : ℕ → ℝ)
    (hX : 0 < X) (hA : 0 < A)
    (hx : x ∈ Icc X (2 * X)) (hδ : δ ∈ Icc 0 (1 / 2))
    (hε : ε ∈ Ioo 0 (1 / 4))
    (hσ : 1 < σ) (hσtwo : σ ≤ 2) (hH : 0 < H)
    (hlo : 1 ≤ lowerCutoff X A)
    (hs : ∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A) :
    ‖normalization * continuousBand s weight
        (lowerCutoff X A) (upperCutoff X A) ε (-H) H σ δ x -
      smoothedMain s weight ε δ x‖ ≤
      256 * (x * δ) * x ^ (σ - 1) *
        coefficientMass s (fun d => (weight d : ℂ)) σ / H := by
  let S : ℝ := (lowerCutoff X A : ℝ) ^ (1 - σ) +
    (upperCutoff X A : ℝ) ^ (1 - σ)
  let B : ℝ := (x * δ) * x ^ (σ - 1) *
    coefficientMass s (fun d => (weight d : ℂ)) σ
  let g : ℝ := Real.log 2 / 2
  have hhi : 1 ≤ upperCutoff X A :=
    le_trans hlo (cutoff_strict X A hX hA).le
  have hS : S ≤ 2 := by
    dsimp [S]
    have ha := Real.rpow_le_one_of_one_le_of_nonpos
      (show (1 : ℝ) ≤ lowerCutoff X A by exact_mod_cast hlo) (by linarith : 1 - σ ≤ 0)
    have hb := Real.rpow_le_one_of_one_le_of_nonpos
      (show (1 : ℝ) ≤ upperCutoff X A by exact_mod_cast hhi) (by linarith : 1 - σ ≤ 0)
    linarith
  have hB : 0 ≤ B := by
    dsimp [B]
    have hxpos : 0 < x := hX.trans_le hx.1
    have hwidth : 0 ≤ x * δ := mul_nonneg hxpos.le hδ.1
    exact mul_nonneg (mul_nonneg hwidth (by positivity))
      (mass_nonnegative s (fun d => (weight d : ℂ)) σ)
  have hg : 0 < g := by dsimp [g]; positivity
  have hden : 0 < g * H := mul_pos hg hH
  have hloghalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    linarith
  have hgquarter : 1 / 4 ≤ g := by dsimp [g]; linarith
  have hnum : 2 * ((x * δ) * (16 * x ^ (σ - 1) * S) *
      coefficientMass s (fun d => (weight d : ℂ)) σ) ≤ 64 * B := by
    have hSmargin : 0 ≤ 2 - S := by linarith
    have hh := mul_nonneg hSmargin hB
    dsimp [B] at hh ⊢
    nlinarith
  have hratio : (64 * B) / (g * H) ≤ (256 * B) / H := by
    apply (div_le_div_iff₀ hden hH).mpr
    have hh := mul_nonneg (show 0 ≤ 4 * g - 1 by linarith)
      (mul_nonneg hB hH.le)
    nlinarith
  calc
    _ ≤ 2 * ((x * δ) * (16 * x ^ (σ - 1) * S) *
        coefficientMass s (fun d => (weight d : ℂ)) σ / (g * H)) := by
      simpa only [S, g] using truncation_bound X A x δ ε σ H s weight
        hX hA hx hδ hε hσ hσtwo hH hlo hs
    _ = (2 * ((x * δ) * (16 * x ^ (σ - 1) * S) *
        coefficientMass s (fun d => (weight d : ℂ)) σ)) / (g * H) := by ring
    _ ≤ (64 * B) / (g * H) := div_le_div_of_nonneg_right hnum hden.le
    _ ≤ (256 * B) / H := hratio
    _ = _ := by dsimp [B]; ring

theorem eventually_power_bound (η : ℝ) (hη : 0 < η) :
    ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
      ∀ (A x Y ε H : ℝ) (s : Finset ℕ) (weight : ℕ → ℝ),
        1 ≤ A → 1 ≤ lowerCutoff X A →
        (∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 4 * A) →
        (∀ d ∈ s, |weight d| ≤ X ^ (η / 4)) →
        x ∈ Icc X (2 * X) → 0 ≤ Y → Y ≤ X / 2 →
        ε ∈ Ioo 0 (1 / 4) → X ^ η ≤ H →
        ‖normalization * continuousBand s weight
            (lowerCutoff X A) (upperCutoff X A) ε (-H) H
            (1 + 1 / Real.log X) (Y / X) x -
          smoothedMain s weight ε (Y / X) x‖ ≤
            Y * X ^ (-(η / 2)) := by
  filter_upwards [PolynomialLogEnvelope.eventually_constant_bound
    (4096 * Real.exp 1) (η / 4) (by positivity) (by linarith),
    eventually_ge_atTop (Real.exp 1)] with X hc hX
  refine ⟨hX, ?_⟩
  intro A x Y ε H s weight hA hlo hs hw hx hY hYhalf hε hH
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hX
  have hxpos : 0 < x := hXp.trans_le hx.1
  have hlog : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hσ : 1 < 1 + 1 / Real.log X := by
    have hh : 0 < 1 / Real.log X := by positivity
    linarith
  have hσtwo : 1 + 1 / Real.log X ≤ 2 := by
    have hh : 1 / Real.log X ≤ 1 := (div_le_one (by linarith)).mpr hlog
    linarith
  have hδ : Y / X ∈ Icc (0 : ℝ) (1 / 2) := by
    constructor
    · exact div_nonneg hY hXp.le
    · exact (div_le_iff₀ hXp).mpr (by linarith)
  have hHpos : 0 < H := (Real.rpow_pos_of_pos hXp _).trans_le hH
  have hmass := FourfoldCoefficientMass.real_weight_mass_bound s A (X ^ (η / 4))
    (1 + 1 / Real.log X) weight hA (by positivity) hσ.le hs hw
  have hspace := CofactorPowerError.spatial_power_bound X x hX hx
  have hraw := truncation_bound_simple X A x (Y / X) ε
    (1 + 1 / Real.log X) H s weight hXp (by linarith) hx hδ hε
    hσ hσtwo hHpos hlo hs
  have hxpower : x * x ^ ((1 + 1 / Real.log X) - 1) =
      x ^ (1 + 1 / Real.log X) := by
    conv_lhs => lhs; rw [← Real.rpow_one x]
    rw [← Real.rpow_add hxpos]
    congr 1
    ring
  have hraw' : ‖normalization * continuousBand s weight
      (lowerCutoff X A) (upperCutoff X A) ε (-H) H
      (1 + 1 / Real.log X) (Y / X) x -
      smoothedMain s weight ε (Y / X) x‖ ≤
        256 * (Y / X) * x ^ (1 + 1 / Real.log X) *
          coefficientMass s (fun d => (weight d : ℂ)) (1 + 1 / Real.log X) / H := by
    convert hraw using 1
    rw [← hxpower]
    ring
  have hInv : H⁻¹ ≤ X ^ (-η) := by
    have hh := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hXp _) hH
      (by norm_num : (-1 : ℝ) ≤ 0)
    rw [Real.rpow_neg_one, ← Real.rpow_mul hXp.le] at hh
    convert hh using 1; ring
  calc
    _ ≤ 256 * (Y / X) * x ^ (1 + 1 / Real.log X) *
        coefficientMass s (fun d => (weight d : ℂ)) (1 + 1 / Real.log X) / H :=
      hraw'
    _ ≤ 256 * (Y / X) * (4 * X * Real.exp 1) * (4 * X ^ (η / 4)) / H := by
      have hmassnonneg := mass_nonnegative s
        (fun d => (weight d : ℂ)) (1 + 1 / Real.log X)
      gcongr
    _ = (4096 * Real.exp 1) * Y * X ^ (η / 4) * H⁻¹ := by
      field_simp
      ring
    _ ≤ (4096 * Real.exp 1) * Y * X ^ (η / 4) * X ^ (-η) := by
      gcongr
    _ ≤ X ^ (η / 4) * Y * X ^ (η / 4) * X ^ (-η) := by
      gcongr
      exact hc.2
    _ = Y * X ^ (-(η / 2)) := by
      calc
        _ = Y * ((X ^ (η / 4) * X ^ (η / 4)) * X ^ (-η)) := by ring
        _ = Y * X ^ (η / 4 + η / 4 + -η) := by
          rw [← Real.rpow_add hXp, ← Real.rpow_add hXp]
        _ = _ := by congr 1; ring

end FourfoldContinuousTruncation

run_cmd do
  for target in [``FourfoldContinuousTruncation.phase_eq,
      ``FourfoldContinuousTruncation.phase_gaps,
      ``FourfoldContinuousTruncation.truncation_bound,
      ``FourfoldContinuousTruncation.truncation_bound_simple,
      ``FourfoldContinuousTruncation.eventually_power_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "FOURFOLD CONTINUOUS TRUNCATION PASSED"
