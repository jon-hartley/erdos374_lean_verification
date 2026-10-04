import TripleFlatContourEnergy
import FactoredCofactorTailWindow

/-! Both exact smoothed divisor contours from the flat-cofactor energy.
Real coefficient signs and convolution multiplicities are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace TripleFlatContour
open Erdos374.HarmanGram152 SmoothedWindowTransfer HarmanProductTailWindow

theorem eventually_bound (η ρ : ℝ) (k : ℕ)
    (hη : 0 < η) (hρ : 0 < ρ) (hρone : ρ < 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
        ∀ (lo hi M N : ℕ) (sm sn : Finset ℕ)
          (am an : ℕ → ℝ) (U Y εs : ℝ),
          1 ≤ lo → ((2 ^ k * lo : ℕ) : ℝ) ≤ X → hi ≤ 2 ^ k * lo →
          X ^ η * U ^ (2 / 7 : ℝ) ≤ (lo : ℝ) →
          2 * X ^ ρ ≤ U → U ≤ X →
          1 ≤ M → (M : ℝ) ≤ X → U ≤ (M : ℝ) ^ 4 →
          1 ≤ N → (N : ℝ) ≤ X → U ≤ (N : ℝ) ^ 2 →
          0 ≤ Y → Y < X → εs ∈ Ioo 0 1 →
          (∀ n ∈ sm, M ≤ n ∧ n ≤ 2 * M) →
          (∀ n ∈ sn, N ≤ n ∧ n ≤ 2 * N) →
          (∑ n ∈ sm, (am n) ^ 2) ≤ X ^ ε * M →
          (∑ n ∈ sn, (an n) ^ 2) ≤ X ^ ε * N →
          (1 / X) * (∫ x in Icc X (2 * X),
            ‖HarmanDivisorContour.productTransform
              (FactoredDivisorWeights.support sm sn)
              (FactoredDivisorWeights.coefficient sm sn am an) lo hi
              εs (X ^ ρ) U (1 + 1 / Real.log X) (Y / X) x‖ ^ 2) ≤
                Y ^ 2 * X ^ (-c) ∧
          (1 / X) * (∫ x in Icc X (2 * X),
            ‖HarmanDivisorContour.productTransform
              (FactoredDivisorWeights.support sm sn)
              (FactoredDivisorWeights.coefficient sm sn am an) lo hi
              εs (-U) (-(X ^ ρ)) (1 + 1 / Real.log X) (Y / X) x‖ ^ 2) ≤
                Y ^ 2 * X ^ (-c) := by
  obtain ⟨γ, hγ, ε, hε, htail⟩ :=
    TripleFlatContourEnergy.eventually_positive_energy η ρ k hη hρ hρone
  refine ⟨γ / 2, by positivity, ε, hε, ?_⟩
  filter_upwards [htail, SmoothedWindowTransfer.eventually_bound
    MellinSmoothingFunction.smoothing MellinSmoothingFunction.differentiable
    MellinSmoothingFunction.support MellinSmoothingFunction.nonnegative
    MellinSmoothingFunction.mass_one γ hγ] with X hp hw
  refine ⟨hw.1, ?_⟩
  intro lo hi M N sm sn am an U Y εs hlo hcap hhi hlength hUlow hUX
    hM hMX hUM hN hNX hUN hY hYX hεs hsm hsn hem hen
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hw.1
  have hH : 0 < X ^ ρ := Real.rpow_pos_of_pos hXp _
  have hHU : X ^ ρ ≤ U := by linarith
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
  have hpositive := hp.2 lo hi M N sm sn
    (fun n => (am n : ℂ)) (fun n => (an n : ℂ)) U (1 + 1 / Real.log X)
    hlo hcap hhi hlength hUlow hUX hσ hM hMX hUM hN hNX hUN hsm hsn
    (by simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hem)
    (by simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hen)
  have hnegative : (∫ t in Icc (-U) (-(X ^ ρ)),
      ‖product lo hi sm sn am an (1 + 1 / Real.log X) t‖ ^ 2) ≤ X ^ (-γ) := by
    unfold product
    rw [RealFrequencyReflection.product_negative_eq_positive
      (Finset.Ioc lo hi) sm sn am an (1 + 1 / Real.log X) (X ^ ρ) U hHU]
    exact hpositive
  constructor
  · simpa only [FactoredCofactorTailWindow.productTransform_eq] using
      hw.2 Y εs (X ^ ρ) U _ hY hYX hεs hHU (by linarith) hF hpositive
  · simpa only [FactoredCofactorTailWindow.productTransform_eq] using
      hw.2 Y εs (-U) (-(X ^ ρ)) _ hY hYX hεs (by linarith) (by linarith)
        hF hnegative

run_cmd do
  for ax in (← Lean.collectAxioms ``eventually_bound) do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"

end TripleFlatContour
