import SmoothedCountBoundary

/-!
An explicit bound on the smoothing boundary mass for uniformly bounded
nonnegative coefficients. The additive one accounts for the possibility
that even a very narrow closed interval contains an integer.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace BoundaryMassBound

theorem cardinality (s : Finset ℕ) (u v : ℝ) (huv : u ≤ v)
    (hs : ∀ n ∈ s, u ≤ (n : ℝ) ∧ (n : ℝ) ≤ v) :
    (s.card : ℝ) ≤ v - u + 1 := by
  classical
  by_cases hne : s.Nonempty
  · have hminmax := s.min'_le_max' hne
    have hsubset : s ⊆ Finset.Icc (s.min' hne) (s.max' hne) := by
      intro n hn
      exact Finset.mem_Icc.mpr ⟨s.min'_le n hn, s.le_max' n hn⟩
    have hcard := Finset.card_le_card hsubset
    rw [Nat.card_Icc] at hcard
    have hnat : s.min' hne ≤ s.max' hne + 1 := by omega
    have hreal : (s.card : ℝ) ≤ (s.max' hne : ℝ) + 1 - (s.min' hne : ℝ) := by
      exact_mod_cast hcard
    have hlow := (hs _ (s.min'_mem hne)).1
    have hhigh := (hs _ (s.max'_mem hne)).2
    linarith
  · have hz : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [hz, Finset.card_empty, Nat.cast_zero]
    linarith

theorem boundary_bound (s : Finset ℕ) (weight : ℕ → ℝ) (ε X W : ℝ)
    (hX : 0 < X) (hε : 0 ≤ ε) (hW : 0 ≤ W)
    (hweight : ∀ n ∈ s, weight n ≤ W) :
    SmoothedCountBoundary.boundary s weight ε X ≤
      W * (4 * Real.log 2 * ε * X + 1) := by
  classical
  let b : Finset ℕ := s.filter (fun n : ℕ => |(n : ℝ) / X - 1| ≤ (2 * Real.log 2) * ε)
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hwidth : 0 ≤ (2 * Real.log 2) * ε * X := by positivity
  have hcard : (b.card : ℝ) ≤ 4 * Real.log 2 * ε * X + 1 := by
    have hh := cardinality b (X - (2 * Real.log 2) * ε * X)
      (X + (2 * Real.log 2) * ε * X) (by linarith) (by
        intro n hn
        have hb := (Finset.mem_filter.mp hn).2
        have habs := abs_le.mp hb
        have hlow := (le_div_iff₀ hX).mp (show 1 - (2 * Real.log 2) * ε ≤ (n : ℝ) / X by linarith)
        have hhigh := (div_le_iff₀ hX).mp (show (n : ℝ) / X ≤ 1 + (2 * Real.log 2) * ε by linarith)
        constructor <;> nlinarith)
    nlinarith
  calc
    _ = ∑ n ∈ b, weight n := by
      unfold SmoothedCountBoundary.boundary b
      rw [Finset.sum_filter]
    _ ≤ ∑ _n ∈ b, W := Finset.sum_le_sum (fun n hn => hweight n (Finset.mem_filter.mp hn).1)
    _ = W * (b.card : ℝ) := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcard hW

end BoundaryMassBound

#print axioms BoundaryMassBound.boundary_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``BoundaryMassBound.boundary_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "BOUNDARY MASS BOUND PASSED"
