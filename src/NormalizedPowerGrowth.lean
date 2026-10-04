import PowerEnvelope
import MomentGrowthEnvelope
import MomentCutoffEnvelope
import NormalizedPowerMoment
import NormalizedDyadicCap

/-!
Arbitrarily small power growth of actual moments of a fixed polynomial
power. The moment order p varies uniformly over the closed interval
[2,3]. Coefficient energy supplies the supremum cap, and the cutoff
envelope supplies the actual band-count bound.

This follows the assembly in NormalizedEvenEnvelope and FlatMixedSaving.
It proves an analytic estimate under the stated support, energy, and
length conditions; it does not identify terms of a sieve decomposition.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace NormalizedPowerGrowth
open Erdos374.HarmanGram152 NormalizedPowerLevel DyadicLevelParameters
open PowerMomentParameters SupremumMoment MomentThreshold MomentLengthRatio

theorem eventually_bound (h : ℕ) (hh : 1 ≤ h) (γ : ℝ) (hγ : 0 < γ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      ∀ (s : Finset ℕ) (N : ℕ) (coeff : ℕ → ℂ) (a T σ p : ℝ),
        1 ≤ N → (N : ℝ) ≤ X → 1 ≤ T → T ≤ X → 1 ≤ σ →
        2 ≤ p → p ≤ 3 →
        T ^ (4 : ℕ) ≤ ((N : ℝ) ^ h) ^ (p + 2) →
        (∀ n ∈ s, N < n ∧ n ≤ 2 * N) →
        (∑ n ∈ s, ‖coeff n‖ ^ 2) ≤ X ^ ε * N →
        (∫ t in Icc a (a + T),
          ‖verticalDirichlet152 s coeff σ t‖ ^ ((h : ℝ) * p)) ≤
          X ^ γ := by
  let δ := γ / 4
  let α := δ / (100 * ((h : ℝ) + 1))
  let u := (h : ℝ) * α / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hα : 0 < α := by dsimp [α]; positivity
  have hhr : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hαidentity : ((h : ℝ) + 1) * α = δ / 100 := by
    dsimp [α]
    field_simp
  have huδ : u ≤ δ := by dsimp [u]; nlinarith [hαidentity]
  obtain ⟨D, hD, C, hC, hmoment⟩ :=
    NormalizedPowerMoment.integral_bound h hh α hα
  let c := min 1 (PowerMomentParameters.sexticConstant h * D ^ 3)
  have hc : 0 < c := by
    dsimp [c, PowerMomentParameters.sexticConstant]
    positivity
  have hc1 : c ≤ 1 := min_le_left _ _
  refine ⟨α, hα, ?_⟩
  filter_upwards [PowerEnvelope.eventually_bound D C h δ hD hC hh hδ,
    MomentCutoffEnvelope.eventually_band_bound c (2 * (h : ℝ)) δ u δ
      hc hc1 (by positivity) hu hδ,
    PolynomialLogEnvelope.eventually_constant_bound 26 δ (by norm_num) hδ]
    with X hp hb hcst
  refine ⟨hp.1, ?_⟩
  intro s N coeff a T σ p hN hNX hT hTX hσ hplow hphigh hlength hs he
  have hXp : 0 < X := by linarith [hp.1]
  have hTp : 0 < T := by linarith
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hXα : 0 < X ^ α := Real.rpow_pos_of_pos hXp _
  have hXδ : 0 < X ^ δ := Real.rpow_pos_of_pos hXp _
  let Q : ℝ := (N : ℝ) ^ h
  let E := energyBudget D N h α (X ^ α)
  let A := quadratic (N ^ h) h T E
  let B := sextic (N ^ h) h T E
  let V := meanEven C N h T α α X
  let U := X ^ u
  let J := bandCountBound (cutoff B (X ^ δ) p) U
  have hQ : 1 ≤ Q := one_le_pow₀ hNR
  have hE : 0 < E := budget_positive D N h α (X ^ α) hD hN hXα
  have hA : 0 ≤ A := quadratic_nonnegative _ _ _ _ hTp.le hE.le
  have hB : 0 < B := sextic_positive _ _ _ _ (one_le_pow₀ hN) hh hTp hE
  have hlog : 0 ≤ Real.log (2 * (N : ℝ)) := Real.log_nonneg (by linarith)
  have hV : 0 ≤ V := by dsimp [V, meanEven]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hJ : 0 ≤ J := bandCountBound_nonneg _ _
  have hparams := hp.2 N T hN hNX hT hTX
  have hBupper : B ≤ X ^ δ * T / Q ^ 2 := by
    dsimp [Q]
    rw [← pow_mul, Nat.mul_comm h 2]
    exact hparams.2.1
  have hBlower : c / X ^ (2 * (h : ℝ)) ≤ B := by
    have hsmall : c / X ^ (2 * h : ℕ) ≤
        PowerMomentParameters.sexticConstant h * D ^ 3 / X ^ (2 * h : ℕ) :=
      div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
    have hlow := hsmall.trans
      (PowerParameterEnvelope.sextic_lower D N h T X α α
        hD hN hNX hT hα.le hα.le)
    simpa only [← Real.rpow_natCast, Nat.cast_mul, Nat.cast_ofNat] using hlow
  have hbands : J ≤ X ^ δ := hb.2 B U p hplow hphigh hBlower le_rfl
  have hcap : ∀ t ∈ Icc a (a + T),
      ‖verticalDirichlet152 s coeff σ t‖ ^ h ≤ U := by
    intro t ht
    have hn := NormalizedDyadicCap.norm_le_rpow s N coeff σ t X α
      hN hσ hXp hs he
    apply (pow_le_pow_left₀ (norm_nonneg _) hn h).trans_eq
    rw [← Real.rpow_mul_natCast hXp.le]
    dsimp [U, u]
    congr 1
    ring
  have hpower : U ^ (p - 2) ≤ X ^ δ := by
    dsimp [U]
    rw [← Real.rpow_mul hXp.le]
    apply Real.rpow_le_rpow_of_exponent_le hp.1
    have hh := mul_le_mul_of_nonneg_left
      (show p - 2 ≤ 1 by linarith) hu
    nlinarith
  have hgrowth := MomentGrowthEnvelope.bound X δ Q T p A B V J
    hp.1 hδ hQ hTp hplow hphigh hlength hA hB hV hJ
    hparams.1 hBupper hparams.2.2 hbands
  calc
    _ ≤ (B / X ^ δ) ^ ratioExponent p * V +
        J * (2 : ℝ) ^ p * (A * (2 : ℝ) ^ (p - 2) + 1) * X ^ δ :=
      hmoment s N coeff a T (X ^ α) σ U p (X ^ δ)
        hN hTp hXα hσ hU hplow (by linarith) hXδ hs he hcap hpower
    _ ≤ 26 * X ^ (3 * δ) := hgrowth
    _ ≤ X ^ δ * X ^ (3 * δ) :=
      mul_le_mul_of_nonneg_right hcst.2 (by positivity)
    _ = X ^ γ := by
      rw [← Real.rpow_add hXp]
      congr 1
      dsimp [δ]
      ring

end NormalizedPowerGrowth

#print axioms NormalizedPowerGrowth.eventually_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``NormalizedPowerGrowth.eventually_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "NORMALIZED POWER GROWTH PASSED"
