import TripleAdoptEighthMomentDecay
import TripleAdoptEighthPowerEnvelope
import TripleAdoptEighthCutoffEnvelope

/-!
A power saving for the eighth moment of the actual flat polynomial.
The length condition is N >= X^eta T^(2/7). Constants and the saving
are fixed before X, and the time interval stays away from zero.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set

namespace TripleAdoptFlatEighthSaving
open Erdos374.HarmanGram152 NormalizedPowerLevel DyadicLevelParameters
open SupremumMoment MomentThreshold FlatEighthMoment

theorem range_from_length (X N T η : ℝ) (hX : 1 ≤ X) (hη : 0 ≤ η)
    (hT : 1 ≤ T) (hN : X ^ η * T ^ (2 / 7 : ℝ) ≤ N) :
    X ^ η ≤ N ∧ T ^ 2 * (X ^ η) ^ 7 ≤ N ^ 7 := by
  have hXp : 0 < X := by linarith
  have hTp : 0 < T := by linarith
  have hZ : 1 ≤ X ^ η := Real.one_le_rpow hX hη
  have hTpow : 1 ≤ T ^ (2 / 7 : ℝ) := Real.one_le_rpow hT (by norm_num)
  refine ⟨(le_mul_of_one_le_right (by positivity) hTpow).trans hN, ?_⟩
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ X ^ η * T ^ (2 / 7 : ℝ)) hN 7
  have hid : (T ^ (2 / 7 : ℝ)) ^ (7 : ℕ) = T ^ (2 : ℕ) := by
    rw [← Real.rpow_mul_natCast hTp.le]
    norm_num
  simpa only [mul_pow, hid, mul_comm] using hh

theorem eventually_bound (η ρ : ℝ) (hη : 0 < η) (hρ : 0 < ρ) (hρone : ρ < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      ∀ (N lo hi : ℕ) (a T σ : ℝ),
        X ^ η * T ^ (2 / 7 : ℝ) ≤ (N : ℝ) → (N : ℝ) ≤ X →
        N ≤ lo → hi ≤ 2 * N → 1 ≤ T → T ≤ X → 1 ≤ σ →
        (∀ t ∈ Icc a (a + T), X ^ ρ ≤ |t| ∧ |t| ≤ X) →
        (∫ t in Icc a (a + T),
          ‖verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t‖ ^ (8 : ℕ)) ≤
            X ^ (-c) := by
  obtain ⟨κ, hκ, hκη, D, hD, C, hC, hflat⟩ :=
    FlatEighthMoment.eventually_bound η ρ hη hρ hρone.le
  have hfactor : 0 ≤ TripleAdoptEighthMomentDecay.fixedFactor := by
    unfold TripleAdoptEighthMomentDecay.fixedFactor
    positivity
  refine ⟨κ / 4, by positivity, ?_⟩
  filter_upwards [hflat, TripleAdoptEighthPowerEnvelope.eventually_bound D C κ hD hC hκ,
    TripleAdoptEighthCutoffEnvelope.eventually_band_bound D (κ / 100) κ (κ / 10)
      hD (by positivity) hκ.le (by positivity),
    PolynomialLogEnvelope.eventually_constant_bound TripleAdoptEighthMomentDecay.fixedFactor
      (κ / 4) hfactor (by positivity)] with X hf hp hb hc
  refine ⟨hf.1, ?_⟩
  intro N lo hi a T σ hlength hNX hlo hhi hT hTX hσ htimes
  have hXp : 0 < X := by linarith [hf.1]
  have hrange := range_from_length X N T η hf.1 hη.le hT hlength
  have hN : 1 ≤ N := by
    exact_mod_cast (Real.one_le_rpow hf.1 hη.le).trans hrange.1
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hTp : 0 < T := by linarith
  let E := energyBudget D N 3 (κ / 100) 1
  let Q := quadratic (N ^ 3) 3 T E
  let B := sextic (N ^ 3) 3 T E
  let M := meanSix C N T (κ / 100)
  let J := bandCountBound (cutoff B (X ^ (-κ)) (8 / 3)) (X ^ (-3 * κ))
  have hE : 0 < E := by dsimp [E, energyBudget]; positivity
  have hQ : 0 ≤ Q := quadratic_nonnegative _ _ _ _ hTp.le hE.le
  have hB : 0 < B := sextic_positive _ _ _ _ (one_le_pow₀ hN) (by norm_num) hTp hE
  have hlog : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by linarith)
  have hM : 0 ≤ M := by dsimp [M, meanSix]; positivity
  have hJ : 0 ≤ J := bandCountBound_nonneg _ _
  have hparams := hp.2 N T hN hNX hT hTX
  have hbands := hb.2 N T hN hNX hT
  have hdecay := TripleAdoptEighthMomentDecay.bound X N T κ η Q B M J hf.1 hκ hκη
    hrange.1 hTp.le hrange.2 hQ hB hM hJ
    hparams.1 hparams.2.1 hparams.2.2 hbands
  calc
    _ ≤ upperBound D C N T (κ / 100) X κ :=
      hf.2 N lo hi a T σ hrange.1 hNX hlo hhi hTp hσ htimes
    _ ≤ TripleAdoptEighthMomentDecay.fixedFactor * X ^ (-κ / 2) := hdecay
    _ ≤ X ^ (κ / 4) * X ^ (-κ / 2) :=
      mul_le_mul_of_nonneg_right hc.2 (by positivity)
    _ = X ^ (-(κ / 4)) := by
      rw [← Real.rpow_add hXp]
      congr 1
      ring

end TripleAdoptFlatEighthSaving

#print axioms TripleAdoptFlatEighthSaving.eventually_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``TripleAdoptFlatEighthSaving.eventually_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "FLAT EIGHTH SAVING PASSED"
