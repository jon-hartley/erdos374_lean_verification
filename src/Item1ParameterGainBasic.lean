import Item1ParameterCore
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace Item1ParameterGain
open Item1ParameterCore

theorem gain_nonneg (a x : ℝ) : 0 ≤ gain a x := le_max_left _ _

theorem model_gain_identity (a x : ℝ) : 2*x/3-modelExponent a x = gain a x := by
  unfold modelExponent gain
  rw [← max_sub_sub_left, sub_self, ← min_sub_sub_left, ← min_sub_sub_left]
  have h₁ : 2*x/3-x/3 = x/3 := by ring
  have h₂ : 2*x/3-(a-x/3) = x-a := by ring
  have h₃ : 2*x/3-(x-a) = a-x/3 := by ring
  rw [h₁, h₂, h₃]

theorem le_gain (a x b : ℝ) (h₁ : b ≤ x / 3)
    (h₂ : b ≤ x - a) (h₃ : b ≤ a - x / 3) : b ≤ gain a x := by
  exact (le_min h₁ (le_min h₂ h₃)).trans (le_max_right _ _)

theorem gain_on_middle (a x : ℝ) (hlo : 5*a/4 ≤ x) (hhi : x ≤ 9*a/4) :
    a/4 ≤ gain a x := by
  apply le_gain <;> linarith

theorem degree_ge_five (a : ℝ) (ha : 1 ≤ a) : 5 ≤ degree a := by
  have hr : (3:ℝ) ≤ Nat.ceil (3*a) := (by linarith : (3:ℝ) ≤ 3*a).trans (Nat.le_ceil _)
  have hc : 3 ≤ Nat.ceil (3*a) := by exact_mod_cast hr
  unfold degree
  omega

theorem degree_lt_three_add (a : ℝ) (ha : 0 ≤ a) :
    (degree a : ℝ) < 3*a+3 := by
  have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ 3*a)
  simp only [degree, Nat.cast_add, Nat.cast_ofNat]
  linarith

theorem degree_le_six (a : ℝ) (ha : 1 ≤ a) : (degree a : ℝ) ≤ 6*a := by
  have hc := degree_lt_three_add a (by linarith)
  linarith

theorem degree_le_nine_halves (a : ℝ) (ha : 2 ≤ a) :
    (degree a : ℝ) ≤ 9*a/2 := by
  have hc := degree_lt_three_add a (by linarith)
  linarith

theorem etaLoss_le (d : ℕ) (hd : 1 ≤ d) : etaLoss d ≤ (d:ℝ)^2/150 := by
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0:ℝ) < d := by linarith
  have hdne : (d:ℝ) ≠ 0 := ne_of_gt hdpos
  have hbase : 0 ≤ 1-1/(d:ℝ) := by
    have := (div_le_one hdpos).2 hd'
    linarith
  have hp := pow_le_pow_left₀ hbase (Real.one_sub_le_exp_neg (1/(d:ℝ))) (4*d)
  rw [← Real.exp_nat_mul] at hp
  have harg : ((4*d:ℕ):ℝ) * -(1/(d:ℝ)) = -4 := by
    push_cast
    field_simp
  rw [harg] at hp
  have hexp : (50:ℝ) ≤ Real.exp 4 := by
    have he : (8/3:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have he4 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 8/3) he 4
    have heq : Real.exp 4 = Real.exp 1 ^ 4 := by simp [← Real.exp_nat_mul]
    rw [heq]
    norm_num at he4 ⊢
    linarith
  have hneg : Real.exp (-4) ≤ (1/50:ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 50) hexp
  have hp' := hp.trans hneg
  unfold etaLoss
  calc
    (d:ℝ)^2/3 * (1-1/(d:ℝ))^(4*d) ≤ (d:ℝ)^2/3 * (1/50) :=
      mul_le_mul_of_nonneg_left hp' (by positivity)
    _ = (d:ℝ)^2/150 := by ring

end Item1ParameterGain

run_cmd do
  for target in [``Item1ParameterGain.gain_nonneg, ``Item1ParameterGain.model_gain_identity,
      ``Item1ParameterGain.le_gain,
      ``Item1ParameterGain.gain_on_middle, ``Item1ParameterGain.degree_ge_five,
      ``Item1ParameterGain.degree_lt_three_add, ``Item1ParameterGain.degree_le_six,
      ``Item1ParameterGain.degree_le_nine_halves, ``Item1ParameterGain.etaLoss_le] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "PARAMETER GAIN BASIC: 9 standard-axiom theorem guards passed."
