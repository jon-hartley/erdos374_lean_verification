import DirectMovingEnergyModulation

/-! Low derivative energy and high base energy from the checked fixed-width
energy theorem. All estimates apply to the already collected signed base
coefficients, preserving every collision. -/
set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Erdos374.DirectMovingEnergy
open PairSpacingRational PairSpacingCollectedEnergy

theorem subset_modulation_energy_le (Q F : ℕ) (a : ℕ → ℝ) (B h : ℝ)
    (hB : 0 ≤ B) (hh : 0 ≤ h)
    (ha : ∀ n ∈ Finset.Icc 1 Q, |a n| ≤ B)
    (S : Finset ℝ) (hS : S ⊆ frequencies Q F) :
    (∑ ξ ∈ S, ‖modulation ξ h * baseCoefficient Q F a ξ‖^2) ≤
      B^2*h*SingletonHarmonic.harmonicSum Q^3 := by
  apply le_trans _ (modulation_energy_le Q F a B h hB hh ha)
  exact Finset.sum_le_sum_of_subset_of_nonneg hS (by intros; positivity)

theorem low_energy_le (Q F : ℕ) (a : ℕ → ℝ) (B H : ℝ)
    (hB : 0 ≤ B) (hH : 0 < H)
    (ha : ∀ n ∈ Finset.Icc 1 Q, |a n| ≤ B) :
    (∑ ξ ∈ lowFrequencies Q F H,
      ‖(2*Real.pi*Complex.I*ξ : ℂ) * baseCoefficient Q F a ξ‖^2) ≤
      4*B^2*SingletonHarmonic.harmonicSum Q^3/H := by
  have hpoint (ξ : ℝ) (hξ : ξ ∈ lowFrequencies Q F H) :
      H^2 * ‖(2*Real.pi*Complex.I*ξ : ℂ)*baseCoefficient Q F a ξ‖^2 ≤
        4*‖modulation ξ H * baseCoefficient Q F a ξ‖^2 := by
    have hh := low_modulation_bound ξ H hH (Finset.mem_filter.mp hξ).2
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ H*‖(2*Real.pi*Complex.I*ξ : ℂ)‖) hh 2
    have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg ‖baseCoefficient Q F a ξ‖)
    simpa only [norm_mul, mul_pow, show (2:ℝ)^2=4 by norm_num, mul_assoc] using hm
  have hs := Finset.sum_le_sum hpoint
  simp only [←Finset.mul_sum] at hs
  have he := subset_modulation_energy_le Q F a B H hB hH.le ha
    (lowFrequencies Q F H) (Finset.filter_subset ..)
  have hsum : H^2 * (∑ ξ ∈ lowFrequencies Q F H,
      ‖(2*Real.pi*Complex.I*ξ : ℂ)*baseCoefficient Q F a ξ‖^2) ≤
        4*(B^2*H*SingletonHarmonic.harmonicSum Q^3) :=
    hs.trans (mul_le_mul_of_nonneg_left he (by norm_num))
  apply (le_div_iff₀ hH).mpr
  nlinarith

theorem high_energy_le (Q F : ℕ) (a : ℕ → ℝ) (B H : ℝ)
    (hB : 0 ≤ B) (hH : 0 < H)
    (ha : ∀ n ∈ Finset.Icc 1 Q, |a n| ≤ B) :
    (∑ ξ ∈ highFrequencies Q F H, ‖baseCoefficient Q F a ξ‖^2) ≤
      2*B^2*H*SingletonHarmonic.harmonicSum Q^3 := by
  let S := highFrequencies Q F H
  let b := baseCoefficient Q F a
  have hinterval : (0:ℝ) ≤ 4*H := by positivity
  have hc (ξ : ℝ) : Continuous (fun h => ‖modulation ξ h * b ξ‖^2) := by
    exact ((modulation_continuous ξ).mul continuous_const).norm.pow 2
  have hc' : Continuous (fun h => ∑ ξ ∈ S, ‖modulation ξ h * b ξ‖^2) :=
    continuous_finsetSum S (fun ξ _ => hc ξ)
  have hb : Continuous (fun h : ℝ => B^2*h*SingletonHarmonic.harmonicSum Q^3) := by
    fun_prop
  have hint :
      4*H * (∑ ξ ∈ S, ‖b ξ‖^2) ≤
        8*B^2*H^2*SingletonHarmonic.harmonicSum Q^3 := by
    calc
      _ = ∑ ξ ∈ S, (4*H)*‖b ξ‖^2 := Finset.mul_sum ..
      _ ≤ ∑ ξ ∈ S, (∫ h in (0:ℝ)..4*H, ‖modulation ξ h‖^2)*‖b ξ‖^2 := by
        apply Finset.sum_le_sum
        intro ξ hξ
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact high_modulation_integral ξ H hH (le_of_lt
          (lt_of_not_ge (Finset.mem_filter.mp hξ).2))
      _ = ∫ h in (0:ℝ)..4*H, ∑ ξ ∈ S, ‖modulation ξ h*b ξ‖^2 := by
        rw [intervalIntegral.integral_finsetSum (fun ξ _ => (hc ξ).intervalIntegrable _ _)]
        apply Finset.sum_congr rfl
        intro ξ hξ
        simp only [norm_mul, mul_pow, intervalIntegral.integral_mul_const]
      _ ≤ ∫ h in (0:ℝ)..4*H, B^2*h*SingletonHarmonic.harmonicSum Q^3 := by
        apply intervalIntegral.integral_mono_on hinterval
          (hc'.intervalIntegrable _ _) (hb.intervalIntegrable _ _)
        intro h hh
        exact subset_modulation_energy_le Q F a B h hB hh.1 ha S (Finset.filter_subset ..)
      _ = _ := by
        rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
          integral_id]
        ring
  dsimp [S, b] at hint
  nlinarith

run_cmd do
  for decl in [``subset_modulation_energy_le, ``low_energy_le, ``high_energy_le] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "COLLECTED LOW DERIVATIVE AND HIGH BASE ENERGIES PASSED"

end Erdos374.DirectMovingEnergy
