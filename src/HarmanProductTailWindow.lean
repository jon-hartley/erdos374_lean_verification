import RealFrequencyReflection
import SmoothedWindowTransfer

/-!
Both frequency tails of the actual smoothed three-factor product,
with real signed coefficients controlled by their squared energies.
Reflection is used for the polynomial energy, then each transform is
bounded on its own interval. No transform monotonicity is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace HarmanProductTailWindow
open Erdos374.HarmanGram152 SmoothedWindowTransfer

def product (Klo Khi : ℕ) (sm sn : Finset ℕ) (am an : ℕ → ℝ)
    (σ t : ℝ) : ℂ :=
  verticalDirichlet152 (Finset.Ioc Klo Khi) (fun _ => 1) σ t *
    verticalDirichlet152 sm (fun n => (am n : ℂ)) σ t *
      verticalDirichlet152 sn (fun n => (an n : ℂ)) σ t

theorem eventually_bound (ell nu e ρ η : ℝ)
    (hell : 0 < ell) (hnu : 0 < nu) (he : 0 < e)
    (hρ : 0 < ρ) (hρell : ρ ≤ ell) (hρone : ρ < 1)
    (hη : 0 < η) (hηρ : η ≤ ρ) :
    ∃ c : ℝ, 0 < c ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
        ∀ (K lo hi M N : ℕ) (sm sn : Finset ℕ)
          (am an : ℕ → ℝ) (H U Y εs : ℝ),
          X ^ ell ≤ (K : ℝ) → (K : ℝ) ≤ X → K ≤ lo → hi ≤ 2 * K →
          1 ≤ M → (M : ℝ) ≤ X → 1 ≤ N → (N : ℝ) ≤ X →
          X ^ nu ≤ (N : ℝ) →
          X ^ (e / 10) * U ^ (10 / 9 : ℝ) ≤ (K * M * N : ℕ) →
          X ^ e * U ^ (6 / 7 : ℝ) ≤ max (K * M : ℕ) (M * N : ℕ) →
          X ^ η ≤ H → H ≤ U → 2 * X ^ ρ ≤ U → U ≤ X →
          0 ≤ Y → Y < X → εs ∈ Ioo 0 1 →
          (∀ n ∈ sm, M < n ∧ n ≤ 2 * M) →
          (∀ n ∈ sn, N < n ∧ n ≤ 2 * N) →
          (∑ n ∈ sm, (am n) ^ 2) ≤ X ^ ε * M →
          (∑ n ∈ sn, (an n) ^ 2) ≤ X ^ ε * N →
          (1 / X) * (∫ x in Icc X (2 * X),
            ‖transform (product lo hi sm sn am an (1 + 1 / Real.log X))
              MellinSmoothingFunction.smoothing εs H U
                (1 + 1 / Real.log X) (Y / X) x‖ ^ 2) ≤ Y ^ 2 * X ^ (-c) ∧
          (1 / X) * (∫ x in Icc X (2 * X),
            ‖transform (product lo hi sm sn am an (1 + 1 / Real.log X))
              MellinSmoothingFunction.smoothing εs (-U) (-H)
                (1 + 1 / Real.log X) (Y / X) x‖ ^ 2) ≤ Y ^ 2 * X ^ (-c) := by
  obtain ⟨γ, hγ, ε, hε, htail⟩ := HarmanProductTail.eventually_positive_energy
    ell nu e ρ η hell hnu he hρ hρell hρone hη hηρ
  refine ⟨γ / 2, by positivity, ε, hε, ?_⟩
  filter_upwards [htail, SmoothedWindowTransfer.eventually_bound
    MellinSmoothingFunction.smoothing MellinSmoothingFunction.differentiable
    MellinSmoothingFunction.support MellinSmoothingFunction.nonnegative
    MellinSmoothingFunction.mass_one γ hγ] with X hp hw
  refine ⟨hw.1, ?_⟩
  intro K lo hi M N sm sn am an H U Y εs hKlow hKX hlo hhi
    hM hMX hN hNX hNlow hproduct hpair hHlow hHU hUlow hUX
    hY hYX hεs hsm hsn hem hen
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hw.1
  have hH : 0 < H := (Real.rpow_pos_of_pos hXp _).trans_le hHlow
  have hlog : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hw.1
  have hσ : 1 ≤ 1 + 1 / Real.log X := by
    have hh : 0 ≤ 1 / Real.log X := by positivity
    linarith
  have hF : Continuous (product lo hi sm sn am an (1 + 1 / Real.log X)) := by
    unfold product
    apply Continuous.mul
    · apply Continuous.mul
      · apply NormalizedMeanSquare.continuous_vertical
        intro n hn
        have hh := (Finset.mem_Ioc.mp hn).1
        omega
      · apply NormalizedMeanSquare.continuous_vertical
        intro n hn
        have hh := (hsm n hn).1
        omega
    · apply NormalizedMeanSquare.continuous_vertical
      intro n hn
      have hh := (hsn n hn).1
      omega
  have hpositive := hp.2 K lo hi M N sm sn
    (fun n => (am n : ℂ)) (fun n => (an n : ℂ)) H U (1 + 1 / Real.log X)
    hKlow hKX hlo hhi hM hMX hN hNX hNlow hproduct hpair
    hHlow hHU hUlow hUX hσ hsm hsn
    (by simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hem)
    (by simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hen)
  have hnegative : (∫ t in Icc (-U) (-H),
      ‖product lo hi sm sn am an (1 + 1 / Real.log X) t‖ ^ 2) ≤ X ^ (-γ) := by
    unfold product
    rw [RealFrequencyReflection.product_negative_eq_positive
      (Finset.Ioc lo hi) sm sn am an (1 + 1 / Real.log X) H U hHU]
    exact hpositive
  constructor
  · exact hw.2 Y εs H U _ hY hYX hεs hHU (by linarith) hF hpositive
  · exact hw.2 Y εs (-U) (-H) _ hY hYX hεs (by linarith) (by linarith)
      hF hnegative

end HarmanProductTailWindow

#print axioms HarmanProductTailWindow.eventually_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``HarmanProductTailWindow.eventually_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "HARMAN PRODUCT TAIL WINDOW PASSED"
