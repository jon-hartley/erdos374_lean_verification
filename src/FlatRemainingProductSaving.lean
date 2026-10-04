import FinitePowerGrowth
import NormalizedProductGrowth
import MomentOrderUpgrade
import RealProductHolder
import PairedMomentOrder
import FlatPowerCap
import PowerOrderParameters

/-!
The branch where the large pair is M*N and the flat K is left over.
All supports, energies, frequency bands, and length inequalities are
explicit application premises.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace FlatRemainingProductSaving
open Erdos374.HarmanGram152 HarmanMomentSelection PairedMomentOrder

theorem pair_length_transfer (X T Q beta ξ η : ℝ)
    (hX : 1 ≤ X) (hT : 1 ≤ T) (hTX : T ≤ X)
    (hbeta : 8 ≤ beta) (hξ : 0 ≤ ξ) (hξη : ξ ≤ η)
    (hQ : X ^ η * T ^ (4 / (2 + pairedOrder beta)) ≤ Q) :
    T ^ (4 : ℕ) ≤ Q ^ (pairedOrder (beta + ξ) + 2) := by
  have hTp : 0 < T := by linarith
  have hXp : 0 < X := by linarith
  let p := pairedOrder (beta + ξ)
  have hp : 2 < p := (conjugate (beta + ξ) (by linarith)).1
  have hshift : T ^ (4 / (2 + p)) ≤
      T ^ (4 / (2 + pairedOrder beta) + ξ) :=
    Real.rpow_le_rpow_of_exponent_le hT
      (threshold_shift beta ξ hbeta hξ)
  have hξT : T ^ ξ ≤ X ^ ξ :=
    Real.rpow_le_rpow hTp.le hTX hξ
  have hξηX : X ^ ξ ≤ X ^ η :=
    Real.rpow_le_rpow_of_exponent_le hX hξη
  have hnew : T ^ (4 / (2 + p)) ≤ Q := by
    calc
      _ ≤ T ^ (4 / (2 + pairedOrder beta) + ξ) := hshift
      _ = T ^ (4 / (2 + pairedOrder beta)) * T ^ ξ :=
        Real.rpow_add hTp _ _
      _ ≤ T ^ (4 / (2 + pairedOrder beta)) * X ^ ξ :=
        mul_le_mul_of_nonneg_left hξT (by positivity)
      _ ≤ T ^ (4 / (2 + pairedOrder beta)) * X ^ η :=
        mul_le_mul_of_nonneg_left hξηX (by positivity)
      _ ≤ Q := by simpa only [mul_comm] using hQ
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ T ^ (4 / (2 + p)))
    hnew (by linarith : 0 ≤ p + 2)
  rw [← Real.rpow_mul hTp.le] at hpow
  have hid : 4 / (2 + p) * (p + 2) = 4 := by
    have hp0 : 2 + p ≠ 0 := by linarith
    field_simp
    ring
  rw [hid] at hpow
  change T ^ (4 : ℕ) ≤ Q ^ (p + 2)
  norm_num at hpow ⊢
  exact hpow

theorem eventually_bound (ell η ρ : ℝ) (H : ℕ)
    (hell : 0 < ell) (hη : 0 < η) (hρ : 0 < ρ)
    (hρone : ρ ≤ 1) (hH : 4 ≤ H) :
    ∃ c : ℝ, 0 < c ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
        ∀ (K lo hi M N h : ℕ) (sM sN : Finset ℕ)
          (coeffM coeffN : ℕ → ℂ) (a T σ beta : ℝ),
          X ^ ell ≤ (K : ℝ) → (K : ℝ) ≤ X →
          K ≤ lo → hi ≤ 2 * K →
          1 ≤ M → (M : ℝ) ≤ X →
          1 ≤ N → (N : ℝ) ≤ X →
          4 ≤ h → h ≤ H →
          2 * (h : ℝ) ≤ beta → beta ≤ 2 * (h : ℝ) + 2 →
          1 ≤ T → T ≤ X → 1 ≤ σ →
          T ^ (4 : ℕ) ≤ (K : ℝ) ^ (beta + 2 * h) →
          X ^ η * T ^ (4 / (2 + pairedOrder beta)) ≤ (M * N : ℕ) →
          (∀ n ∈ sM, M < n ∧ n ≤ 2 * M) →
          (∀ n ∈ sN, N < n ∧ n ≤ 2 * N) →
          (∑ n ∈ sM, ‖coeffM n‖ ^ 2) ≤ X ^ ε * M →
          (∑ n ∈ sN, ‖coeffN n‖ ^ 2) ≤ X ^ ε * N →
          (∀ t ∈ Icc a (a + T), X ^ ρ ≤ |t| ∧ |t| ≤ X) →
          (∫ t in Icc a (a + T),
            ‖verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t *
              verticalDirichlet152 sM coeffM σ t *
                verticalDirichlet152 sN coeffN σ t‖ ^ (2 : ℕ)) ≤
              X ^ (-c) := by
  obtain ⟨k, hk, hk1, hflat⟩ :=
    FlatPowerCap.eventually_bound ell ρ 1 hell hρ hρone (by norm_num)
  let ξ : ℝ := min (η / 2) 1
  let B : ℝ := 2 * (H : ℝ) + 3
  let γ : ℝ := k * ξ / B
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  have hξη : ξ ≤ η := by dsimp [ξ]; linarith [min_le_left (η / 2) 1]
  have hξone : ξ ≤ 1 := min_le_right _ _
  have hB : 0 < B := by dsimp [B]; positivity
  have hγ : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨εK, hεK, hpower⟩ := FinitePowerGrowth.eventually_bound H γ hγ
  obtain ⟨εMN, hεMN, hproduct⟩ := NormalizedProductGrowth.eventually_bound γ hγ
  let ε := min εK εMN
  have hε : 0 < ε := lt_min hεK hεMN
  refine ⟨γ, hγ, ε, hε, ?_⟩
  filter_upwards [hflat, hpower, hproduct] with X hf hpow hprod
  refine ⟨hf.1, ?_⟩
  intro K lo hi M N h sM sN coeffM coeffN a T σ beta
    hKlow hKX hlo hhi hM hMX hN hNX hh hHbound hbetaLo hbetaHi
    hT hTX hσ hlengthK hlengthMN hsM hsN heM heN htimes
  have hXp : 0 < X := by linarith [hf.1]
  have hK : 1 ≤ K := by
    exact_mod_cast (Real.one_le_rpow hf.1 hell.le).trans hKlow
  have hsk : ∀ n ∈ Finset.Ioc lo hi, K < n ∧ n ≤ 2 * K := by
    intro n hn
    have hm := Finset.mem_Ioc.mp hn
    omega
  have hek : (∑ n ∈ Finset.Ioc lo hi, ‖(1 : ℂ)‖ ^ 2) ≤
      X ^ ε * K := by
    simp only [norm_one, one_pow, Finset.sum_const, nsmul_eq_mul,
      mul_one, Nat.card_Ioc]
    have hcard : (hi - lo : ℕ) ≤ K := by omega
    have hεone : 1 ≤ X ^ ε := Real.one_le_rpow hf.1 hε.le
    exact_mod_cast (show (hi - lo : ℕ) ≤ (K : ℝ) by exact_mod_cast hcard) |>.trans
      (le_mul_of_one_le_left (Nat.cast_nonneg K) hεone)
  have hβeight : 8 ≤ beta := by
    have hhr : (4 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  have hβp : 0 < beta := by linarith
  have hβBound : beta + ξ ≤ B := by
    have hhr : (h : ℝ) ≤ H := by exact_mod_cast hHbound
    dsimp [B]
    linarith
  let beta' := beta + ξ
  let tau' := pairedOrder beta'
  have hβ' : 2 < beta' := by dsimp [beta']; linarith
  have htau' : 2 < tau' := (conjugate beta' hβ').1
  have hconj : 2 / beta' + 2 / tau' = 1 := by
    have hh := (conjugate beta' hβ').2
    linarith
  have htau3 : tau' ≤ 3 := by
    have hupper : beta' ≤ 2 * ((H + 1 : ℕ) : ℝ) + 2 := by
      dsimp [beta', B] at hβBound ⊢
      push_cast
      linarith
    exact (bounds (H + 1) beta' (by omega) (by dsimp [beta']; linarith)
      hupper).2
  have horder := PowerOrderParameters.bounds h beta (by omega) hbetaLo hbetaHi
  have hlengthPow : T ^ (4 : ℕ) ≤
      ((K : ℝ) ^ h) ^ (beta / (h : ℝ) + 2) := by
    rw [PowerOrderParameters.length_identity K h beta (by positivity) (by omega)]
    exact hlengthK
  have hlenMN : T ^ (4 : ℕ) ≤
      (M * N : ℕ) ^ (tau' + 2) :=
    pair_length_transfer X T (M * N : ℕ) beta ξ η hf.1 hT hTX
      hβeight hξ.le hξη hlengthMN
  have hpowerEnergy : (∑ n ∈ Finset.Ioc lo hi, ‖(1 : ℂ)‖ ^ 2) ≤
      X ^ εK * K :=
    hek.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hf.1 (min_le_left εK εMN))
      (Nat.cast_nonneg K))
  have hMEnergy : (∑ n ∈ sM, ‖coeffM n‖ ^ 2) ≤ X ^ εMN * M :=
    heM.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hf.1 (min_le_right εK εMN))
      (Nat.cast_nonneg M))
  have hNEnergy : (∑ n ∈ sN, ‖coeffN n‖ ^ 2) ≤ X ^ εMN * N :=
    heN.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hf.1 (min_le_right εK εMN))
      (Nat.cast_nonneg N))
  let FK := verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ
  let FM := verticalDirichlet152 sM coeffM σ
  let FN := verticalDirichlet152 sN coeffN σ
  let GMN := fun t => FM t * FN t
  have hFKcont : ContinuousOn FK (Icc a (a + T)) :=
    (NormalizedMeanSquare.continuous_vertical _ _ σ
      (fun n hn => by have hh := (hsk n hn).1; omega)).continuousOn
  have hMcont : ContinuousOn FM (Icc a (a + T)) :=
    (NormalizedMeanSquare.continuous_vertical _ _ σ
      (fun n hn => by have hh := (hsM n hn).1; omega)).continuousOn
  have hNcont : ContinuousOn FN (Icc a (a + T)) :=
    (NormalizedMeanSquare.continuous_vertical _ _ σ
      (fun n hn => by have hh := (hsN n hn).1; omega)).continuousOn
  have hMNcont : ContinuousOn GMN (Icc a (a + T)) := hMcont.mul hNcont
  have hflatcap : ∀ t ∈ Icc a (a + T), ‖FK t‖ ≤ X ^ (-k) := by
    intro t ht
    exact hf.2 K lo hi hKlow hKX hlo hhi t σ
      (htimes t ht).1 (htimes t ht).2 hσ
  have hmomentK : (∫ t in Icc a (a + T), ‖FK t‖ ^ beta) ≤ X ^ γ := by
    have hh := hpow.2 h (by omega) hHbound (Finset.Ioc lo hi) K
      (fun _ => 1) a T σ (beta / (h : ℝ)) hK hKX hT hTX hσ
      horder.1 horder.2 hlengthPow hsk hpowerEnergy
    simpa only [PowerOrderParameters.order_identity h beta (by omega)] using hh
  have hmomentK' : (∫ t in Icc a (a + T), ‖FK t‖ ^ beta') ≤
      X ^ (γ - k * ξ) := by
    have hh := MomentOrderUpgrade.bound_of_moment a (a + T) X k beta ξ γ
      FK hXp hk.le hβp hξ.le hFKcont hflatcap hmomentK
    simpa only [beta'] using hh
  have hmomentMN : (∫ t in Icc a (a + T), ‖GMN t‖ ^ tau') ≤ X ^ γ :=
    hprod.2 M N sM sN coeffM coeffN a T σ tau'
      hM hN hMX hNX hT hTX hσ htau'.le htau3 hlenMN
      hsM hsN hMEnergy hNEnergy
  have hholder := RealProductHolder.bound_of_moments a (a + T)
    beta' tau' X (γ - k * ξ) γ FK GMN
    hβ' htau' hconj hXp hFKcont hMNcont hmomentK' hmomentMN
  have hweight : 2 / B ≤ 2 / beta' := by
    have hβB : beta' ≤ B := hβBound
    apply (div_le_div_iff₀ hB (by linarith : 0 < beta')).mpr
    nlinarith
  have hcost : 2 * γ ≤ k * ξ * (2 / beta') := by
    calc
      _ = k * ξ * (2 / B) := by dsimp [γ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hweight (mul_nonneg hk.le hξ.le)
  have hexponent : (γ - k * ξ) * (2 / beta') + γ * (2 / tau') ≤ -γ := by
    calc
      _ = γ * (2 / beta' + 2 / tau') - k * ξ * (2 / beta') := by ring
      _ = γ - k * ξ * (2 / beta') := by rw [hconj]; ring
      _ ≤ -γ := by linarith
  calc
    _ = (∫ t in Icc a (a + T), ‖FK t * GMN t‖ ^ (2 : ℕ)) := by
      congr 1
      ext t
      simp only [FK, GMN, FM, FN, mul_assoc]
    _ ≤ X ^ ((γ - k * ξ) * (2 / beta') + γ * (2 / tau')) := hholder
    _ ≤ X ^ (-γ) := Real.rpow_le_rpow_of_exponent_le hf.1 hexponent

end FlatRemainingProductSaving

#print axioms FlatRemainingProductSaving.pair_length_transfer
#print axioms FlatRemainingProductSaving.eventually_bound
run_cmd do
  for target in [``FlatRemainingProductSaving.pair_length_transfer,
      ``FlatRemainingProductSaving.eventually_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "FLAT REMAINING PRODUCT SAVING PASSED"
