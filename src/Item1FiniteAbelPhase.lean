import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

/-!
Finite Abel summation for the exact prefix convention. No cancellation input is
proved by this file. All weights and every partial sum are explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
namespace Item1FiniteAbelPhase

def «prefix» (a : ℕ → ℂ) (N : ℕ) : ℂ := ∑ n ∈ Finset.range N, a n

theorem prefix_succ (a : ℕ → ℂ) (N : ℕ) :
    «prefix» a (N+1) = «prefix» a N + a N := by
  exact Finset.sum_range_succ a N

theorem difference_telescope (w : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (w n-w (n+1))) = w 0-w N := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; ring

/-- Includes the final endpoint weight; no integral approximation is used. -/
theorem weighted_identity (a : ℕ → ℂ) (w : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (N+1), (w n:ℂ)*a n) =
      (w N:ℂ)*«prefix» a (N+1) +
        ∑ n ∈ Finset.range N, ((w n-w (n+1):ℝ):ℂ)*«prefix» a (n+1) := by
  induction N with
  | zero => simp [«prefix»]
  | succ N ih =>
      rw [Finset.sum_range_succ (f := fun n => (w n:ℂ)*a n), ih,
        Finset.sum_range_succ (f := fun n =>
          ((w n-w (n+1):ℝ):ℂ)*«prefix» a (n+1)), prefix_succ a (N+1)]
      push_cast
      ring

/-- Supremum over ALL prefixes, not just the full block. The constant is one. -/
theorem weighted_prefix_bound (a : ℕ → ℂ) (w : ℕ → ℝ) (N : ℕ) (B : ℝ)
    (hB : 0≤B) (hw : ∀ n, 0≤w n) (hm : Antitone w)
    (hp : ∀ k≤N, ‖«prefix» a k‖≤B) :
    ‖∑ n ∈ Finset.range N, (w n:ℂ)*a n‖ ≤ B*w 0 := by
  cases N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
            exact mul_nonneg hB (hw 0)
  | succ N =>
      rw [weighted_identity]
      have hdiff (n : ℕ) : 0≤w n-w (n+1) := sub_nonneg.mpr (hm (Nat.le_succ n))
      calc
        _ ≤ ‖(w N:ℂ)*«prefix» a (N+1)‖ +
            ∑ n ∈ Finset.range N, ‖((w n-w (n+1):ℝ):ℂ)*«prefix» a (n+1)‖ :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
        _ ≤ w N*B + ∑ n ∈ Finset.range N, (w n-w (n+1))*B := by
          apply add_le_add
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw N)]
            exact mul_le_mul_of_nonneg_left (hp (N+1) le_rfl) (hw N)
          · apply Finset.sum_le_sum
            intro n hn
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hdiff n)]
            exact mul_le_mul_of_nonneg_left
              (hp (n+1) (by have := Finset.mem_range.mp hn; omega)) (hdiff n)
        _ = B*w 0 := by
          rw [←Finset.sum_mul, difference_telescope]
          ring

/-- Exact complete dyadic partition of the prefix [0,2^J).
The n=0 term is displayed, so it cannot be silently used as a positive integer. -/
theorem dyadic_partition (a : ℕ → ℂ) (J : ℕ) :
    (∑ n ∈ Finset.range (2^J), a n) = a 0 +
      ∑ j ∈ Finset.range J, ∑ n ∈ Finset.range (2^j), a (2^j+n) := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [pow_succ, Nat.mul_two, Finset.sum_range_add, ih, Finset.sum_range_succ]
      simp only [Nat.add_comm]
      ring

end Item1FiniteAbelPhase

run_cmd do
  for target in [``Item1FiniteAbelPhase.prefix_succ,
    ``Item1FiniteAbelPhase.difference_telescope, ``Item1FiniteAbelPhase.weighted_identity,
    ``Item1FiniteAbelPhase.weighted_prefix_bound, ``Item1FiniteAbelPhase.dyadic_partition] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Item1FiniteAbelPhase.weighted_prefix_bound
#print axioms Item1FiniteAbelPhase.dyadic_partition
