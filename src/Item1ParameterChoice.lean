import Item1ParameterCore

/-! The concrete positive interval and the integer-rounded one-third scale. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators

namespace Item1ParameterChoice

def scale (M : ℕ) : ℕ := Nat.floor ((M:ℝ)^(1/3:ℝ))

def positiveSet (A : ℕ) : Finset ℕ := Finset.Icc 1 A

theorem positiveSet_card (A : ℕ) : (positiveSet A).card = A := by
  simp [positiveSet, Nat.card_Icc]

theorem positiveSet_mem (A b : ℕ) : b ∈ positiveSet A ↔ 1 ≤ b ∧ b ≤ A := by
  simp [positiveSet]

theorem positiveSet_nonempty {A : ℕ} (hA : 1 ≤ A) : (positiveSet A).Nonempty := by
  exact ⟨1, (positiveSet_mem A 1).mpr ⟨le_rfl, hA⟩⟩

theorem cube_root_cube (M : ℕ) : (((M:ℝ)^(1/3:ℝ))^3) = (M:ℝ) := by
  rw [← Real.rpow_mul_natCast (show (0:ℝ) ≤ M by positivity)]
  norm_num

theorem scale_bounds {M : ℕ} (hM : 8 ≤ M) :
    1 ≤ scale M ∧ (M:ℝ)^(1/3:ℝ)/2 ≤ (scale M:ℝ) ∧
    (scale M:ℝ) ≤ (M:ℝ)^(1/3:ℝ) ∧ 2*(scale M*scale M) ≤ M := by
  let z : ℝ := (M:ℝ)^(1/3:ℝ)
  have hz0 : 0 ≤ z := Real.rpow_nonneg (by positivity) _
  have hz3 : z^3 = (M:ℝ) := cube_root_cube M
  have hM8 : (8:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have hz2 : 2 ≤ z := by
    by_contra hn
    have hlt : z < 2 := lt_of_not_ge hn
    have hh := pow_lt_pow_left₀ hlt hz0 (by norm_num : (3:ℕ) ≠ 0)
    norm_num at hh
    linarith
  have hA : 1 ≤ scale M := Nat.le_floor (by simpa only [Nat.cast_one] using (show (1:ℝ) ≤ z by linarith))
  have hA1 : (1:ℝ) ≤ (scale M:ℝ) := by exact_mod_cast hA
  have hupper : (scale M:ℝ) ≤ z := Nat.floor_le hz0
  have hstrict : z < (scale M:ℝ)+1 := Nat.lt_floor_add_one z
  have hlower : z/2 ≤ (scale M:ℝ) := by linarith
  have hsq : (scale M:ℝ)^2 ≤ z^2 := pow_le_pow_left₀ (by positivity) hupper 2
  have htwo : 2*(scale M:ℝ)*(scale M:ℝ) ≤ (M:ℝ) := by
    have hprod := mul_nonneg (sub_nonneg.mpr hz2) (sq_nonneg z)
    nlinarith
  have hreal : (2:ℝ)*((scale M:ℝ)*(scale M:ℝ)) ≤ (M:ℝ) := by
    simpa only [mul_assoc] using htwo
  have hnat : 2*(scale M*scale M) ≤ M := by exact_mod_cast hreal
  exact ⟨hA, hlower, hupper, hnat⟩

end Item1ParameterChoice

run_cmd do
  for target in [``Item1ParameterChoice.positiveSet_card,
      ``Item1ParameterChoice.positiveSet_mem,
      ``Item1ParameterChoice.positiveSet_nonempty,
      ``Item1ParameterChoice.cube_root_cube,
      ``Item1ParameterChoice.scale_bounds] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "PARAMETER CHOICE: 5 standard-axiom theorem guards passed."
