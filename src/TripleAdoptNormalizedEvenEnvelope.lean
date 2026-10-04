import NormalizedEvenMoment
import EighthMomentParameters
import PolynomialLogEnvelope

/-!
For T <= N^k, every fixed even moment has arbitrarily small power growth.
A small positive coefficient-energy loss is allowed and quantified.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace TripleAdoptNormalizedEvenEnvelope
open Erdos374.HarmanGram152

theorem eventually_bound (k : ℕ) (hk : 1 ≤ k) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      ∀ (s : Finset ℕ) (N : ℕ) (coeff : ℕ → ℂ) (a T σ : ℝ),
        1 ≤ N → (N : ℝ) ≤ X → 0 ≤ T → T ≤ (N : ℝ) ^ k → 1 ≤ σ →
        (∀ n ∈ s, N ≤ n ∧ n ≤ 2 * N) →
        (∑ n ∈ s, ‖coeff n‖ ^ 2) ≤ X ^ ε * N →
        (∫ t in Icc a (a + T), ‖verticalDirichlet152 s coeff σ t‖ ^ (2 * k)) ≤
          X ^ δ := by
  let ε := δ / (2 * ((k : ℝ) + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨D, hD, hm⟩ := NormalizedEvenMoment.integral_bound k hk ε hε
  let B : ℝ := 1 + 4 * (2 : ℝ) ^ k * (1 + k)
  let C : ℝ := D * (2 : ℝ) ^ ε * B
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨ε, hε, ?_⟩
  filter_upwards [PolynomialLogEnvelope.eventually_bound C 1 (δ / 2) hC (by positivity)]
    with X hX
  refine ⟨hX.1, ?_⟩
  intro s N coeff a T σ hN hNX hT hTN hσ hs henergy
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hXp : 0 < X := by linarith [hX.1]
  have hlog := EighthMomentParameters.log_bounds N 1 X hNR hNX
    (by norm_num) hX.1
  let G := 1 + Real.log X
  have hG : 1 ≤ G := hlog.1
  have hlogN : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by linarith)
  have hratio : T / (N : ℝ) ^ k ≤ 1 := (div_le_one (by positivity)).mpr hTN
  have hbracket : T / (N : ℝ) ^ k + 4 * (2 : ℝ) ^ k * (1 + k * Real.log (2 * N)) ≤
      B * G := by
    have hmult := mul_le_mul_of_nonneg_left hlog.2.1 (Nat.cast_nonneg k)
    have hh := mul_le_mul_of_nonneg_left
      (show 1 + k * Real.log (2 * N) ≤ 1 + k * (1 + Real.log X) by linarith)
      (by positivity : 0 ≤ 4 * (2 : ℝ) ^ k)
    have hrem := mul_nonneg (by positivity : 0 ≤ 1 + 4 * (2 : ℝ) ^ k)
      (show 0 ≤ G - 1 by linarith)
    dsimp [B]
    dsimp [G] at *
    nlinarith
  have hscale : (2 * (N : ℝ)) ^ ε ≤ (2 : ℝ) ^ ε * X ^ ε := by
    rw [← Real.mul_rpow (by norm_num) hXp.le]
    apply Real.rpow_le_rpow (by positivity) (by linarith) hε.le
  have hpow : X ^ ε * (X ^ ε) ^ k = X ^ (δ / 2) := by
    rw [← Real.rpow_mul_natCast hXp.le, ← Real.rpow_add hXp]
    congr 1
    dsimp [ε]
    field_simp
    ring
  calc
    _ ≤ D * (2 * (N : ℝ)) ^ ε * (X ^ ε) ^ k *
        (T / (N : ℝ) ^ k + 4 * (2 : ℝ) ^ k * (1 + k * Real.log (2 * N))) :=
      hm s N coeff a T (X ^ ε) σ hN hT hσ hs henergy
    _ ≤ D * ((2 : ℝ) ^ ε * X ^ ε) * (X ^ ε) ^ k * (B * G) := by
      gcongr
    _ = (C * G) * X ^ (δ / 2) := by dsimp [C]; rw [← hpow]; ring
    _ ≤ X ^ (δ / 2) * X ^ (δ / 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [pow_one] using hX.2
    _ = X ^ δ := by rw [← Real.rpow_add hXp]; congr 1; ring

end TripleAdoptNormalizedEvenEnvelope

#print axioms TripleAdoptNormalizedEvenEnvelope.eventually_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``TripleAdoptNormalizedEvenEnvelope.eventually_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "NORMALIZED EVEN ENVELOPE PASSED"
