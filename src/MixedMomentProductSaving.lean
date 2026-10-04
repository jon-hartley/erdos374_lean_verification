import VariableMixedSaving
import FinitePowerGrowth
import PairedMomentOrder
import PowerOrderParameters
import RealProductHolder

/-!
The K-containing pair branch with a uniformly chosen real moment order.
One cutoff covers every integer power through H and every admissible
beta. All three factors are actual normalized Dirichlet polynomials.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace MixedMomentProductSaving
open Erdos374.HarmanGram152 HarmanMomentSelection

theorem eventually_bound (ell η ρ : ℝ) (H : ℕ)
    (hell : 0 < ell) (hη : 0 < η) (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    (hH : 4 ≤ H) :
    ∃ c : ℝ, 0 < c ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
        ∀ (K lo hi M N h : ℕ) (s r : Finset ℕ) (left right : ℕ → ℂ)
          (a T σ beta : ℝ),
          X ^ ell ≤ (K : ℝ) → (K : ℝ) ≤ X → K ≤ lo → hi ≤ 2 * K →
          1 ≤ M → (M : ℝ) ≤ X → 1 ≤ N → (N : ℝ) ≤ X →
          4 ≤ h → h ≤ H → 2 * (h : ℝ) ≤ beta → beta ≤ 2 * (h : ℝ) + 2 →
          X ^ η * T ^ (4 / (pairedOrder beta + 2)) ≤ (K * M : ℕ) →
          T ^ (4 : ℕ) ≤ (N : ℝ) ^ (beta + 2 * h) →
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
  let gap : ℝ := 1 / ((H : ℝ) + 1)
  have hgap : 0 < gap := by dsimp [gap]; positivity
  have hgap1 : gap ≤ 1 := by
    dsimp [gap]
    exact (div_le_one (by positivity)).mpr (by have hh := Nat.cast_nonneg (α := ℝ) H; linarith)
  obtain ⟨c, hc, εM, hεM, hm⟩ :=
    VariableMixedSaving.eventually_bound ell η ρ gap hell hη hρ hρone hgap hgap1
  obtain ⟨εN, hεN, hn⟩ := FinitePowerGrowth.eventually_bound H (c / 3) (by positivity)
  refine ⟨c / 3, by positivity, min εM εN, lt_min hεM hεN, ?_⟩
  filter_upwards [hm, hn] with X hmX hnX
  refine ⟨hmX.1, ?_⟩
  intro K lo hi M N h s r left right a T σ beta hKlow hKX hlo hhi
    hM hMX hN hNX hh hHmax hbetaLo hbetaHi hpair hsingle hT hTX hσ hs hr heM heN htimes
  have hXp : 0 < X := by linarith [hmX.1]
  have hhr : (4 : ℝ) ≤ h := by exact_mod_cast hh
  have hHcast : (h : ℝ) ≤ H := by exact_mod_cast hHmax
  have hbeta : 8 ≤ beta := by linarith
  have hbetaUpper : beta ≤ 2 * (H : ℝ) + 2 := by linarith
  have horders := PairedMomentOrder.bounds H beta (by omega) hbeta hbetaUpper
  have hconjugate := PairedMomentOrder.conjugate beta (by linarith)
  have henergyM : (∑ n ∈ s, ‖left n‖ ^ 2) ≤ X ^ εM * M :=
    heM.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hmX.1 (min_le_left _ _)) (Nat.cast_nonneg M))
  have henergyN : (∑ n ∈ r, ‖right n‖ ^ 2) ≤ X ^ εN * N :=
    heN.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hmX.1 (min_le_right _ _)) (Nat.cast_nonneg N))
  have hFMoment := hmX.2 K lo hi M s left a T σ (pairedOrder beta)
    hKlow hKX hlo hhi hM hMX horders.1 horders.2 hpair hT hTX hσ hs henergyM htimes
  have hsingle' : T ^ (4 : ℕ) ≤ ((N : ℝ) ^ h) ^ (beta / (h : ℝ) + 2) := by
    rw [PowerOrderParameters.length_identity (N : ℝ) h beta (Nat.cast_nonneg N) (by omega)]
    exact hsingle
  have hp := PowerOrderParameters.bounds h beta (by omega) hbetaLo hbetaHi
  have hGMoment := hnX.2 h (by omega) hHmax r N right a T σ (beta / (h : ℝ))
    hN hNX hT hTX hσ hp.1 hp.2 hsingle' hr henergyN
  rw [PowerOrderParameters.order_identity h beta (by omega)] at hGMoment
  let F := fun t => verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t *
    verticalDirichlet152 s left σ t
  let G := fun t => verticalDirichlet152 r right σ t
  have hF : Continuous F :=
    (NormalizedMeanSquare.continuous_vertical (Finset.Ioc lo hi) (fun _ => 1) σ (by
      intro n hn
      have hn' := (Finset.mem_Ioc.mp hn).1
      omega)).mul
    (NormalizedMeanSquare.continuous_vertical s left σ (by
      intro n hn
      have hn' := (hs n hn).1
      omega))
  have hG : Continuous G := NormalizedMeanSquare.continuous_vertical r right σ (by
    intro n hn
    have hn' := (hr n hn).1
    omega)
  have hholder := RealProductHolder.bound_of_moments a (a + T)
    (pairedOrder beta) beta X (-c) (c / 3) F G hconjugate.1 (by linarith)
    hconjugate.2 hXp hF.continuousOn hG.continuousOn hFMoment hGMoment
  have hpairWeight : 2 / 3 ≤ 2 / pairedOrder beta :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith [hconjugate.1]) horders.2
  have hsingleWeight : 2 / beta ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  have hexponent : -c * (2 / pairedOrder beta) + (c / 3) * (2 / beta) ≤ -(c / 3) := by
    have hh₁ := mul_le_mul_of_nonneg_left hpairWeight hc.le
    have hh₂ := mul_le_mul_of_nonneg_left hsingleWeight (show 0 ≤ c / 3 by positivity)
    nlinarith
  exact hholder.trans (Real.rpow_le_rpow_of_exponent_le hmX.1 hexponent)

end MixedMomentProductSaving

#print axioms MixedMomentProductSaving.eventually_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``MixedMomentProductSaving.eventually_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "MIXED MOMENT PRODUCT SAVING PASSED"
