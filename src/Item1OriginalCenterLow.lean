import Item1PrimeLowSpectrum
import MellinWindowFactor

/-! UNCOMPILED. The endpoint has no PNT, local-psi, bad-spectrum, prime-cap,
low-energy, or Fourier-to-physical hypothesis. The existing PNT theorem and the
retained Abel proof are called through explicit source modules. This does NOT
prove middle frequencies, the physical mean, item 2, or the final Erdos theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
namespace Item1OriginalCenterLow
open Item1SourceLocalArithmetic Item1PrimeLowSpectrum SourceAbelLow
open SourceLiteralMoments SourceLiteralMass SourceCenteredMiddle
open PositiveInteriorModel PositiveInteriorCells

/-- Generic quantitative step; the eventual theorem below constructs both inputs. -/
theorem original_center_pointwise (X t eps : ℝ) (j : ℕ×ℕ)
    (hX : 2≤X) (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X))
    (heps : 0≤eps) (hpsi : LocalPsiError X j eps)
    (hbad : ∀ i : Fin 3, badMass X j i≤eps) :
    ‖originalCentered X j t‖ ≤ 2250*eps*(1+|t|) := by
  rw [original_center_identity]
  have ht := norm_sub_le (centeredProduct X j t)
    (SourceLiteralMiddle.sourceProduct X j t-primeProduct X j t)
  have hfull := centered_pointwise X t eps j hX hlog hj heps hpsi
  have hdel := product_deletion_bound X t eps j hX hlog hj hbad
  have hn : 0≤eps*|t| := mul_nonneg heps (abs_nonneg t)
  nlinarith

theorem finite_low_energy (X T eps : ℝ) (j : ℕ×ℕ)
    (hX : 2≤X) (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X))
    (hT : 1≤T) (heps : 0≤eps) (hpsi : LocalPsiError X j eps)
    (hbad : ∀ i : Fin 3, badMass X j i≤eps) :
    (∫ t in Icc (-T) T, ‖originalCentered X j t‖^2) ≤ 40500000*eps^2*T^3 := by
  have hc := (originalCentered_continuous X j (by linarith)).norm.pow 2
  have hi : IntegrableOn (fun _ : ℝ => (2250*eps*(1+T))^2) (Icc (-T) T) :=
    continuous_const.integrableOn_Icc
  have hm := setIntegral_mono_on hc.integrableOn_Icc hi measurableSet_Icc (by
    intro t ht
    have ht' : |t|≤T := abs_le.mpr ht
    have hb := (original_center_pointwise X t eps j hX hlog hj heps hpsi hbad).trans
      (mul_le_mul_of_nonneg_left (by linarith : 1+|t|≤1+T) (by positivity))
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2)
  rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith : -T≤T),
    smul_eq_mul] at hm
  change (∫ t in Icc (-T) T, ‖originalCentered X j t‖^2) ≤
    (T - -T)*(2250*eps*(1+T))^2 at hm
  have hsq : (1+T)^2≤4*T^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hsq
    (show 0≤2*T*2250^2*eps^2 by positivity)
  nlinarith

/-- The chosen low cutoff lies below the unchanged middle/tail height eventually. -/
theorem eventually_lowCut_le_height (K : ℕ) :
    ∀ᶠ X : ℝ in atTop, lowCut X K≤X^(562/625:ℝ) := by
  have hh := (isLittleO_log_rpow_rpow_atTop (K:ℝ)
    (by norm_num : (0:ℝ)<562/625)).bound (by norm_num : (0:ℝ)<1)
  filter_upwards [hh, eventually_ge_atTop (2:ℝ)] with X hX htwo
  have hXp : 0<X := by linarith
  have hl0 : 0≤Real.log X := Real.log_nonneg (by linarith)
  simpa only [lowCut, Real.rpow_natCast, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hl0 K),
    abs_of_nonneg (Real.rpow_pos_of_pos hXp (562/625:ℝ)).le, one_mul] using hX

/-- Main unweighted low-frequency endpoint. All arithmetic inputs are constructed. -/
theorem eventually_original_center_low (K : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ j∈boxes (mesh X),
      (∫ t in Icc (-lowCut X K) (lowCut X K), ‖originalCentered X j t‖^2) ≤
        40500000/((1+Real.log X)^40*lowCut X K) := by
  have hpsi := eventually_localPsi K
  have hbad := eventually_badMass_budget K
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000000:ℝ))
  filter_upwards [hpsi, hbad, hlog, eventually_ge_atTop (2:ℝ)] with X hp hb hl hX
  intro j hj
  have hT := lowCut_ge_one X K (by linarith)
  have he := budget_pos X K (by linarith)
  have hLp : 0<1+Real.log X := by linarith
  have hTp : 0<lowCut X K := by linarith
  have hm := finite_low_energy X (lowCut X K) (errorBudget X K) j hX hl hj hT
    he.le (hp j hj) (hb j hj)
  convert hm using 1
  unfold errorBudget
  field_simp [ne_of_gt hLp, ne_of_gt hTp]
  <;> ring

/-- Exact source sharp multiplier, normalized by eta. This is the existing
MellinWindowFactor factor, not a newly assumed bounded function. -/
def sharpMultiplier (eta t : ℝ) : ℂ := MellinWindowFactor.factor 1 eta t/(eta:ℂ)

theorem sharp_norm_le_one (eta t : ℝ) (he0 : 0<eta) (he1 : eta<1) :
    ‖sharpMultiplier eta t‖ ≤ 1 := by
  have h := MellinWindowFactor.norm_le_width 1 eta t (by norm_num) he0.le he1
  unfold sharpMultiplier
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he0]
  exact (div_le_iff₀ he0).mpr (by simpa using h)

theorem sharp_continuous (eta : ℝ) (he1 : eta<1) : Continuous (sharpMultiplier eta) :=
  (MellinWindowFactor.continuous_factor 1 eta (by norm_num) he1).div_const _

theorem weighted_low_le (X T eta : ℝ) (j : ℕ×ℕ) (hX : 0<X)
    (he0 : 0<eta) (he1 : eta<1) :
    (∫ t in Icc (-T) T, ‖sharpMultiplier eta t*originalCentered X j t‖^2) ≤
      ∫ t in Icc (-T) T, ‖originalCentered X j t‖^2 := by
  have hf := originalCentered_continuous X j hX
  have hw := ((sharp_continuous eta he1).mul hf).norm.pow 2
  apply setIntegral_mono_on hw.integrableOn_Icc (hf.norm.pow 2).integrableOn_Icc
    measurableSet_Icc
  intro t ht
  have h := mul_le_mul_of_nonneg_right (sharp_norm_le_one eta t he0 he1)
    (norm_nonneg (originalCentered X j t))
  exact pow_le_pow_left₀ (norm_nonneg _)
    (by simpa only [Pi.mul_apply, norm_mul, one_mul] using h) 2

/-- One threshold works for all cells AND all admissible physical widths. -/
theorem eventually_sharp_original_center_low (K : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ j∈boxes (mesh X), ∀ eta : ℝ,
      0<eta → eta<1 →
      (∫ t in Icc (-lowCut X K) (lowCut X K),
        ‖sharpMultiplier eta t*originalCentered X j t‖^2) ≤
        40500000/((1+Real.log X)^40*lowCut X K) := by
  filter_upwards [eventually_original_center_low K, eventually_ge_atTop (2:ℝ)]
    with X hlow hX
  intro j hj eta he0 he1
  exact (weighted_low_le X (lowCut X K) eta j (by linarith) he0 he1).trans (hlow j hj)

/-- Sum over the ACTUAL source cells. No fixed-host count is substituted. -/
theorem eventually_actual_cell_low_sum (K : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ eta : ℝ, 0<eta → eta<1 →
      (∑ j∈boxes (mesh X), ∫ t in Icc (-lowCut X K) (lowCut X K),
        ‖sharpMultiplier eta t*originalCentered X j t‖^2) ≤
        ((boxes (mesh X)).card:ℝ)*40500000/
          ((1+Real.log X)^40*lowCut X K) := by
  filter_upwards [eventually_sharp_original_center_low K] with X hX
  intro eta he0 he1
  have h := Finset.sum_le_sum (fun j hj => hX j hj eta he0 he1)
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_div_assoc] using h

run_cmd do
  for target in [``original_center_pointwise, ``finite_low_energy, ``eventually_lowCut_le_height, ``eventually_original_center_low, ``sharp_norm_le_one, ``sharp_continuous, ``weighted_low_le, ``eventually_sharp_original_center_low, ``eventually_actual_cell_low_sum] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1OriginalCenterLow: 9 original theorem guards passed."

end Item1OriginalCenterLow
