import Erdos374_Update152

/-!
Partial summation for a decreasing nonnegative real weight. The exact
discrete identity is the seed's KusminLandau151.summation_by_parts.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators

namespace MonotoneWeight

theorem antitone_weight_bound (M : ℕ) (c : ℕ → ℂ) (w : ℕ → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hw : ∀ n, 0 ≤ w n) (hm : Antitone w)
    (hprefix : ∀ m ≤ M, ‖∑ n ∈ Finset.range m, c n‖ ≤ R) :
    ‖∑ n ∈ Finset.range M, c n * (w n : ℂ)‖ ≤ R * w 0 := by
  cases M with
  | zero => simpa using mul_nonneg hR (hw 0)
  | succ M =>
    let S : ℕ → ℂ := fun m => ∑ n ∈ Finset.range m, c n
    have hstep : ∀ n, S (n + 1) - S n = c n := by
      intro n
      simp [S, Finset.sum_range_succ]
    have hid := Erdos374.KusminLandau151.summation_by_parts S (fun n => (w n : ℂ)) M
    simp only [hstep] at hid
    have hzero : S 0 = 0 := by simp [S]
    rw [hzero, zero_mul, sub_zero] at hid
    have hdiff : ∀ n, ‖(w (n + 1) : ℂ) - (w n : ℂ)‖ = w n - w (n + 1) := by
      intro n
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr (hm (Nat.le_succ n)))]
      ring
    have hsum : (∑ n ∈ Finset.range M, (w n - w (n + 1))) = w 0 - w M := by
      simpa only [neg_sub_neg] using
        (Finset.sum_range_sub (fun n => -w n) M)
    rw [hid]
    calc
      _ ≤ ‖S (M + 1) * (w M : ℂ)‖ +
          ‖∑ n ∈ Finset.range M, S (n + 1) * ((w (n + 1) : ℂ) - (w n : ℂ))‖ :=
        norm_sub_le _ _
      _ ≤ R * w M + ∑ n ∈ Finset.range M, R * (w n - w (n + 1)) := by
        apply add_le_add
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw M)]
          exact mul_le_mul_of_nonneg_right (hprefix (M + 1) le_rfl) (hw M)
        · apply (norm_sum_le _ _).trans
          apply Finset.sum_le_sum
          intro n hn
          rw [norm_mul, hdiff]
          exact mul_le_mul_of_nonneg_right
            (hprefix (n + 1) (by have := Finset.mem_range.mp hn; omega))
            (sub_nonneg.mpr (hm (Nat.le_succ n)))
      _ = R * w 0 := by rw [← Finset.mul_sum, hsum]; ring

end MonotoneWeight

#print axioms MonotoneWeight.antitone_weight_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``MonotoneWeight.antitone_weight_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "MONOTONE WEIGHT PASSED"
