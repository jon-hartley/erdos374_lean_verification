import FiniteMellinInversion

/-!
The error from replacing a finite weighted count by Smooth1 is supported
near the cutoff. All weights are nonnegative; the boundary mass is kept
explicit rather than presumed small in a short interval.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace SmoothedCountBoundary

def sharp (s : Finset ℕ) (weight : ℕ → ℝ) (X : ℝ) : ℝ :=
  ∑ n ∈ s, if (n : ℝ) ≤ X then weight n else 0

def smooth (s : Finset ℕ) (weight : ℕ → ℝ) (Ψ : ℝ → ℝ) (ε X : ℝ) : ℝ :=
  ∑ n ∈ s, weight n * Smooth1 Ψ ε ((n : ℝ) / X)

def boundary (s : Finset ℕ) (weight : ℕ → ℝ) (ε X : ℝ) : ℝ :=
  ∑ n ∈ s, if |(n : ℝ) / X - 1| ≤ (2 * Real.log 2) * ε then weight n else 0

theorem pointwise (Ψ : ℝ → ℝ) (ε r : ℝ) (hε : ε ∈ Ioo 0 1) (hr : 0 < r)
    (hnonneg : ∀ x > 0, 0 ≤ Ψ x)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ x in Ioi 0, Ψ x / x = 1) :
    |Smooth1 Ψ ε r - (if r ≤ 1 then (1 : ℝ) else 0)| ≤
      if |r - 1| ≤ (2 * Real.log 2) * ε then (1 : ℝ) else 0 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlow := Smooth1Nonneg hnonneg hr hε.1
  have hhigh := Smooth1LeOne hnonneg hmass hε.1 hr
  by_cases hband : |r - 1| ≤ (2 * Real.log 2) * ε
  · rw [ite_eq_left hband]
    split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [ite_eq_right hband]
    have hout : (2 * Real.log 2) * ε < |r - 1| := lt_of_not_ge hband
    by_cases hrone : r ≤ 1
    · rw [ite_eq_left hrone]
      have habs : |r - 1| = 1 - r := by rw [abs_of_nonpos (by linarith)]; ring
      rw [habs] at hout
      obtain ⟨c, _, hc, hbelow⟩ := Smooth1Properties_below hsupport hmass
      have hvalue := hbelow ε r hε.1 hr (by
        rw [hc]
        nlinarith [mul_pos hlog hε.1])
      rw [hvalue]
      norm_num
    · rw [ite_eq_right hrone]
      have habs : |r - 1| = r - 1 := abs_of_nonneg (by linarith)
      rw [habs] at hout
      obtain ⟨c, _, hc, habove⟩ := Smooth1Properties_above hsupport
      have hvalue := habove ε r hε (by rw [hc]; linarith)
      rw [hvalue]
      norm_num

theorem error_bound (s : Finset ℕ) (weight : ℕ → ℝ) (Ψ : ℝ → ℝ) (ε X : ℝ)
    (hX : 0 < X) (hε : ε ∈ Ioo 0 1) (hs : ∀ n ∈ s, 0 < n)
    (hweight : ∀ n ∈ s, 0 ≤ weight n) (hnonneg : ∀ x > 0, 0 ≤ Ψ x)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ x in Ioi 0, Ψ x / x = 1) :
    |smooth s weight Ψ ε X - sharp s weight X| ≤ boundary s weight ε X := by
  unfold smooth sharp boundary
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hs n hn
  have hh := pointwise Ψ ε ((n : ℝ) / X) hε (div_pos hnpos hX) hnonneg hsupport hmass
  have heq : (if (n : ℝ) ≤ X then weight n else 0) =
      weight n * (if (n : ℝ) / X ≤ 1 then 1 else 0) := by
    simp only [div_le_one hX]
    split_ifs <;> ring
  rw [heq, ← mul_sub, abs_mul, abs_of_nonneg (hweight n hn)]
  apply (mul_le_mul_of_nonneg_left hh (hweight n hn)).trans_eq
  split_ifs <;> ring

theorem window_error_bound (s : Finset ℕ) (weight : ℕ → ℝ) (Ψ : ℝ → ℝ)
    (ε L X : ℝ) (hL : 0 < L) (hX : 0 < X) (hε : ε ∈ Ioo 0 1)
    (hs : ∀ n ∈ s, 0 < n) (hweight : ∀ n ∈ s, 0 ≤ weight n)
    (hnonneg : ∀ x > 0, 0 ≤ Ψ x)
    (hsupport : Function.support Ψ ⊆ Icc (1 / 2) 2)
    (hmass : ∫ x in Ioi 0, Ψ x / x = 1) :
    |(smooth s weight Ψ ε X - smooth s weight Ψ ε L) -
      (sharp s weight X - sharp s weight L)| ≤
        boundary s weight ε X + boundary s weight ε L := by
  have hx := error_bound s weight Ψ ε X hX hε hs hweight hnonneg hsupport hmass
  have hl := error_bound s weight Ψ ε L hL hε hs hweight hnonneg hsupport hmass
  rw [show (smooth s weight Ψ ε X - smooth s weight Ψ ε L) -
      (sharp s weight X - sharp s weight L) =
      (smooth s weight Ψ ε X - sharp s weight X) -
      (smooth s weight Ψ ε L - sharp s weight L) by ring]
  exact (abs_sub _ _).trans (add_le_add hx hl)

end SmoothedCountBoundary

#print axioms SmoothedCountBoundary.window_error_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``SmoothedCountBoundary.window_error_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "SMOOTHED COUNT BOUNDARY PASSED"
