import MixedMomentProductSaving
import FlatRemainingProductSaving
import HarmanLengthSelection

/-!
A uniform three-factor estimate under the headline product and pair
length conditions of Harman's Lemma 5. Both choices of the larger pair
are covered. The coefficient, support and frequency conditions remain
explicit, and no sieve decomposition or prime main term is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace HarmanProductSaving
open Erdos374.HarmanGram152

theorem eventually_bound (ell nu e ρ : ℝ)
    (hell : 0 < ell) (hnu : 0 < nu) (he : 0 < e)
    (hρ : 0 < ρ) (hρone : ρ ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ X : ℝ in atTop, 1 < X ∧
        ∀ (K lo hi M N : ℕ) (s r : Finset ℕ) (left right : ℕ → ℂ)
          (a T σ : ℝ),
          X ^ ell ≤ (K : ℝ) → (K : ℝ) ≤ X → K ≤ lo → hi ≤ 2 * K →
          1 ≤ M → (M : ℝ) ≤ X → 1 ≤ N → (N : ℝ) ≤ X → X ^ nu ≤ (N : ℝ) →
          X ^ (e / 10) * T ^ (10 / 9 : ℝ) ≤ (K * M * N : ℕ) →
          X ^ e * T ^ (6 / 7 : ℝ) ≤ max (K * M : ℕ) (M * N : ℕ) →
          1 ≤ T → T ≤ X → 1 ≤ σ →
          (∀ n ∈ s, M < n ∧ n ≤ 2 * M) →
          (∀ n ∈ r, N < n ∧ n ≤ 2 * N) →
          (∑ n ∈ s, ‖left n‖ ^ 2) ≤ X ^ ε * M →
          (∑ n ∈ r, ‖right n‖ ^ 2) ≤ X ^ ε * N →
          (∀ t ∈ Icc a (a + T), X ^ ρ ≤ |t| ∧ |t| ≤ X) →
          (∫ t in Icc a (a + T),
            ‖verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t *
              verticalDirichlet152 s left σ t *
                verticalDirichlet152 r right σ t‖ ^ 2) ≤ X ^ (-c) := by
  let lambda := min ell nu
  have hlambda : 0 < lambda := lt_min hell hnu
  obtain ⟨H, hH, hselect⟩ := HarmanLengthSelection.exists_uniform_order lambda e hlambda he
  obtain ⟨cK, hcK, εK, hεK, hkm⟩ :=
    MixedMomentProductSaving.eventually_bound ell (e / 10) ρ H
      hell (by positivity) hρ hρone hH
  obtain ⟨cN, hcN, εN, hεN, hmn⟩ :=
    FlatRemainingProductSaving.eventually_bound ell (e / 10) ρ H
      hell (by positivity) hρ hρone hH
  refine ⟨min cK cN, lt_min hcK hcN, min εK εN, lt_min hεK hεN, ?_⟩
  filter_upwards [hkm, hmn, eventually_ge_atTop (2 : ℝ)] with X hkX hnX hX2
  have hX : 1 < X := by linarith
  have hXp : 0 < X := by linarith
  refine ⟨hX, ?_⟩
  intro K lo hi M N s r left right a T σ hKlow hKX hlo hhi
    hM hMX hN hNX hNlow hproduct hpair hT hTX hσ hs hr henergyM henergyN htimes
  have hK : 1 ≤ K := by
    exact_mod_cast (Real.one_le_rpow hX.le hell.le).trans hKlow
  have hKp : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  by_cases hchoice : M * N ≤ K * M
  · have hpairK : X ^ e * T ^ (6 / 7 : ℝ) ≤ (K * M : ℕ) := by
      simpa only [max_eq_left hchoice] using hpair
    have hG : X ^ lambda ≤ (N : ℝ) :=
      (Real.rpow_le_rpow_of_exponent_le hX.le (min_le_right ell nu)).trans hNlow
    have htotal : X ^ (e / 10) * T ^ (10 / 9 : ℝ) ≤ (K * M : ℕ) * (N : ℝ) := by
      simpa only [Nat.cast_mul] using hproduct
    obtain ⟨h, beta, hh, hHmax, hloβ, hhiβ, hsingle, hpaired⟩ :=
      hselect X T (K * M : ℕ) N hX hT hTX (by positivity) hNp hG htotal hpairK
    have heM : (∑ n ∈ s, ‖left n‖ ^ 2) ≤ X ^ εK * M :=
      henergyM.trans (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hX.le (min_le_left εK εN)) (Nat.cast_nonneg M))
    have heN : (∑ n ∈ r, ‖right n‖ ^ 2) ≤ X ^ εK * N :=
      henergyN.trans (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hX.le (min_le_left εK εN)) (Nat.cast_nonneg N))
    have hh := hkX.2 K lo hi M N h s r left right a T σ beta
      hKlow hKX hlo hhi hM hMX hN hNX hh hHmax hloβ hhiβ
      hpaired hsingle hT hTX hσ hs hr heM heN htimes
    exact hh.trans (Real.rpow_le_rpow_of_exponent_le hX.le
      (neg_le_neg (min_le_left cK cN)))
  · have hchoice' : K * M ≤ M * N := by omega
    have hpairN : X ^ e * T ^ (6 / 7 : ℝ) ≤ (M * N : ℕ) := by
      simpa only [max_eq_right hchoice'] using hpair
    have hG : X ^ lambda ≤ (K : ℝ) :=
      (Real.rpow_le_rpow_of_exponent_le hX.le (min_le_left ell nu)).trans hKlow
    have htotal : X ^ (e / 10) * T ^ (10 / 9 : ℝ) ≤ (M * N : ℕ) * (K : ℝ) := by
      convert hproduct using 1
      push_cast
      ring
    obtain ⟨h, beta, hh, hHmax, hloβ, hhiβ, hsingle, hpaired⟩ :=
      hselect X T (M * N : ℕ) K hX hT hTX (by positivity) hKp hG htotal hpairN
    have heM : (∑ n ∈ s, ‖left n‖ ^ 2) ≤ X ^ εN * M :=
      henergyM.trans (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hX.le (min_le_right εK εN)) (Nat.cast_nonneg M))
    have heN : (∑ n ∈ r, ‖right n‖ ^ 2) ≤ X ^ εN * N :=
      henergyN.trans (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hX.le (min_le_right εK εN)) (Nat.cast_nonneg N))
    have hpaired' : X ^ (e / 10) * T ^ (4 / (2 + HarmanMomentSelection.pairedOrder beta)) ≤
        (M * N : ℕ) := by simpa only [add_comm] using hpaired
    have hh := hnX.2 K lo hi M N h s r left right a T σ beta
      hKlow hKX hlo hhi hM hMX hN hNX hh hHmax hloβ hhiβ hT hTX hσ
      hsingle hpaired' hs hr heM heN htimes
    exact hh.trans (Real.rpow_le_rpow_of_exponent_le hX.le
      (neg_le_neg (min_le_right cK cN)))

end HarmanProductSaving

#print axioms HarmanProductSaving.eventually_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``HarmanProductSaving.eventually_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "HARMAN PRODUCT SAVING PASSED"
