import OuterMaskFrequencyWork

/-! Quantitative frequency ranges and the exceptional translated low
frequency interval for the actual nine-cutoff separator. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace OuterMaskShiftBoundsWork
open OuterMaskFrequencyWork

theorem shift_bound (ω c : Fin 9 → ℝ) (T : ℝ)
    (hω : ∀n, |ω n| ≤ T) : |shift ω c| ≤ T*∑n,|c n| := by
  calc
    _ ≤ ∑n, |ω n*c n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑n, T*|c n| := Finset.sum_le_sum (fun n _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hω n) (abs_nonneg _))
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem prime_shift_bound (ω : Fin 9 → ℝ) (T : ℝ)
    (hω : ∀n, |ω n| ≤ T) : |shift ω primeSlope| ≤ 9*T := by
  have hh := shift_bound ω primeSlope T hω
  have hc : (∑n : Fin 9, |primeSlope n|) = 9 := by
    norm_num [primeSlope,Fin.sum_univ_succ]
  rw [hc] at hh
  linarith

theorem divisor_shift (ω : Fin 9 → ℝ) : shift ω divisorSlope = ω 8 := by
  simp [shift,divisorSlope,Fin.sum_univ_succ]

theorem prime_shift (ω : Fin 9 → ℝ) : shift ω primeSlope =
    -ω 0+ω 1-ω 2+ω 3+ω 4-ω 5+ω 6-ω 7+ω 8 := by
  simp [shift,primeSlope,Fin.sum_univ_succ]
  ring

theorem first_shift (s : ℝ) (i : ℕ) (ω : Fin 9 → ℝ) :
    shift ω (firstSlope s i) = -3*ω 0+ω 1/s^2+
      ω 4/SieveGeometricGrid.exponent s i-
      ω 5/SieveGeometricGrid.exponent s (i+1)+ω 8 := by
  simp [shift,firstSlope,Fin.sum_univ_succ]
  ring

theorem second_shift (s : ℝ) (j : ℕ) (ω : Fin 9 → ℝ) :
    shift ω (secondSlope s j) = -3*ω 2+ω 3/s^2+
      ω 6/SieveGeometricGrid.exponent s j-
      ω 7/SieveGeometricGrid.exponent s (j+1)+ω 8 := by
  simp [shift,secondSlope,Fin.sum_univ_succ]
  ring

theorem translated_height (t H T : ℝ) (ω : Fin 9 → ℝ)
    (ht : |t| ≤ H) (hω : ∀n, |ω n| ≤ T) :
    |t+shift ω primeSlope| ≤ H+9*T := by
  exact (abs_add_le _ _).trans (add_le_add ht (prime_shift_bound ω T hω))

theorem translated_low_iff (t a U : ℝ) :
    |t+a| ≤ U ↔ t ∈ Set.Icc (-a-U) (-a+U) := by
  rw [abs_le,Set.mem_Icc]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

theorem outside_translated_low (t a U : ℝ)
    (ht : t ∉ Set.Icc (-a-U) (-a+U)) : U < |t+a| := by
  exact lt_of_not_ge (fun hh => ht ((translated_low_iff t a U).mp hh))

run_cmd do
  for decl in [``shift_bound, ``prime_shift_bound, ``divisor_shift, ``prime_shift,
      ``first_shift, ``second_shift, ``translated_height, ``translated_low_iff,
      ``outside_translated_low] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterMaskShiftBoundsWork
