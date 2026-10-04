import TripleAdoptFlatEighthSaving
import TripleAdoptNormalizedEvenEnvelope
import TripleAdoptProductMomentHolder

/-!
A proved long-factor region for a product of three Dirichlet polynomials.
One factor is flat; the other two may have arbitrary complex coefficients
with a small power loss in their squared energy. This is not all of
Harman's three-factor lemma or the prime short-interval theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace TripleAdoptFlatProductSaving
open Erdos374.HarmanGram152

theorem eventually_bound (η ρ : ℝ) (hη : 0 < η) (hρ : 0 < ρ) (hρone : ρ < 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
        ∀ (K lo hi M N : ℕ) (sm sn : Finset ℕ) (am an : ℕ → ℂ) (a T σ : ℝ),
          X ^ η * T ^ (2 / 7 : ℝ) ≤ (K : ℝ) → (K : ℝ) ≤ X →
          K ≤ lo → hi ≤ 2 * K → 1 ≤ T → T ≤ X → 1 ≤ σ →
          (∀ t ∈ Icc a (a + T), X ^ ρ ≤ |t| ∧ |t| ≤ X) →
          1 ≤ M → (M : ℝ) ≤ X → T ≤ (M : ℝ) ^ 4 →
          1 ≤ N → (N : ℝ) ≤ X → T ≤ (N : ℝ) ^ 2 →
          (∀ n ∈ sm, M ≤ n ∧ n ≤ 2 * M) →
          (∀ n ∈ sn, N ≤ n ∧ n ≤ 2 * N) →
          (∑ n ∈ sm, ‖am n‖ ^ 2) ≤ X ^ ε * M →
          (∑ n ∈ sn, ‖an n‖ ^ 2) ≤ X ^ ε * N →
          (∫ t in Icc a (a + T),
            ‖verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t *
              verticalDirichlet152 sm am σ t * verticalDirichlet152 sn an σ t‖ ^ 2) ≤
              X ^ (-c) := by
  obtain ⟨γ, hγ, hflat⟩ := TripleAdoptFlatEighthSaving.eventually_bound η ρ hη hρ hρone
  obtain ⟨εm, hεm, hm⟩ := TripleAdoptNormalizedEvenEnvelope.eventually_bound 4 (by norm_num)
    (γ / 8) (by positivity)
  obtain ⟨εn, hεn, hn⟩ := TripleAdoptNormalizedEvenEnvelope.eventually_bound 2 (by norm_num)
    (γ / 8) (by positivity)
  refine ⟨γ / 8, by positivity, min εm εn, lt_min hεm hεn, ?_⟩
  filter_upwards [hflat, hm, hn] with X hf hm hn
  refine ⟨hf.1, ?_⟩
  intro K lo hi M N sm sn am an a T σ hlength hKX hlo hhi hT hTX hσ htimes
    hM hMX hTM hN hNX hTN hsm hsn hem hen
  have hXp : 0 < X := by linarith [hf.1]
  have hTp : 0 ≤ T := by linarith
  have hKlower := (TripleAdoptFlatEighthSaving.range_from_length X K T η hf.1 hη.le hT hlength).1
  have hKR : (1 : ℝ) ≤ K := (Real.one_le_rpow hf.1 hη.le).trans hKlower
  have hK : 1 ≤ K := by exact_mod_cast hKR
  let F := verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ
  let G := verticalDirichlet152 sm am σ
  let H := verticalDirichlet152 sn an σ
  have hFc : Continuous F := NormalizedMeanSquare.continuous_vertical _ _ _ (by
    intro n hn
    have hh := (Finset.mem_Ioc.mp hn).1
    omega)
  have hGc : Continuous G := NormalizedMeanSquare.continuous_vertical _ _ _ (by
    intro n hn
    have hh := (hsm n hn).1
    omega)
  have hHc : Continuous H := NormalizedMeanSquare.continuous_vertical _ _ _ (by
    intro n hn
    have hh := (hsn n hn).1
    omega)
  have hFbound := hf.2 K lo hi a T σ hlength hKX hlo hhi hT hTX hσ htimes
  have hGbound := hm.2 sm M am a T σ hM hMX hTp hTM hσ hsm
    (hem.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hf.1 (min_le_left εm εn)) (Nat.cast_nonneg M)))
  have hHbound := hn.2 sn N an a T σ hN hNX hTp hTN hσ hsn
    (hen.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hf.1 (min_le_right εm εn)) (Nat.cast_nonneg N)))
  norm_num only [show (2 : ℕ) * 4 = 8 by norm_num] at hGbound
  norm_num only [show (2 : ℕ) * 2 = 4 by norm_num] at hHbound
  have hFG : 0 ≤ ∫ t in Icc a (a + T), ‖F t‖ ^ 8 := integral_nonneg (by intro t; positivity)
  have hGG : 0 ≤ ∫ t in Icc a (a + T), ‖G t‖ ^ 8 := integral_nonneg (by intro t; positivity)
  have hHG : 0 ≤ ∫ t in Icc a (a + T), ‖H t‖ ^ 4 := integral_nonneg (by intro t; positivity)
  have hfour := TripleAdoptProductMomentHolder.eighth_eighth_fourth a (a + T) F G H hFc hGc hHc
  have hpower : (∫ t in Icc a (a + T), ‖F t * G t * H t‖ ^ 2) ^ 4 ≤
      (X ^ (-(γ / 8))) ^ (4 : ℕ) := by
    calc
      _ ≤ (∫ t in Icc a (a + T), ‖F t‖ ^ 8) *
          (∫ t in Icc a (a + T), ‖G t‖ ^ 8) *
          (∫ t in Icc a (a + T), ‖H t‖ ^ 4) ^ 2 := hfour
      _ ≤ X ^ (-γ) * X ^ (γ / 8) * (X ^ (γ / 8)) ^ (2 : ℕ) := by
        gcongr
      _ = X ^ (-5 * γ / 8) := by
        rw [← Real.rpow_mul_natCast hXp.le, ← Real.rpow_add hXp, ← Real.rpow_add hXp]
        congr 1
        norm_num
        ring
      _ ≤ X ^ (-γ / 2) := Real.rpow_le_rpow_of_exponent_le hf.1 (by linarith)
      _ = _ := by
        rw [← Real.rpow_mul_natCast hXp.le]
        congr 1
        norm_num
        ring
  exact le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) (by positivity) hpower

end TripleAdoptFlatProductSaving

#print axioms TripleAdoptFlatProductSaving.eventually_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``TripleAdoptFlatProductSaving.eventually_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "FLAT PRODUCT SAVING PASSED"
