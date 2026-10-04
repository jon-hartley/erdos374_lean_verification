import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! Exact finite weighted even-moment expansion and a correlation bound.
The weights have norm at most one; the phase values need no norm hypothesis.
All statements include exponent zero and empty finite index sets. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Item1WeightedMomentExpansion

theorem norm_even_pow_complex (v : ℂ) (s : ℕ) :
    ((‖v‖ ^ (2 * s) : ℝ) : ℂ) = v ^ s * conj (v ^ s) := by
  simp only [Complex.mul_conj', norm_pow, Complex.ofReal_pow, ← pow_mul,
    Nat.mul_comm s 2]

/-- The weighted power expansion keeps every ordered tuple. -/
theorem weighted_sum_pow {κ η : Type*} [Fintype κ] (s : ℕ)
    (ε : κ → ℂ) (z : κ → η → ℂ) (c : η) :
    (∑ b, ε b * z b c) ^ s =
      ∑ p : Fin s → κ, (∏ l, ε (p l)) * (∏ l, z (p l) c) := by
  classical
  rw [Fintype.sum_pow]
  simp only [Finset.prod_mul_distrib]

/-- Exact expansion with the tuple weights outside each coefficient sum. -/
theorem weighted_moment_expansion {κ η : Type*} [Fintype κ]
    (D : Finset η) (s : ℕ) (ε : κ → ℂ) (z : κ → η → ℂ) :
    ((∑ c ∈ D, ‖∑ b, ε b * z b c‖ ^ (2 * s) : ℝ) : ℂ) =
      ∑ p : Fin s → κ, ∑ q : Fin s → κ,
        ((∏ l, ε (p l)) * conj (∏ l, ε (q l))) *
          (∑ c ∈ D, (∏ l, z (p l) c) * conj (∏ l, z (q l) c)) := by
  classical
  simp only [Complex.ofReal_sum, norm_even_pow_complex, weighted_sum_pow,
    map_sum, map_mul, Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro c hc
  ring

theorem tuple_weight_norm_le {κ : Type*} (s : ℕ) (ε : κ → ℂ)
    (hε : ∀ b, ‖ε b‖ ≤ 1) (p : Fin s → κ) :
    ‖∏ l, ε (p l)‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun l _ => norm_nonneg (ε (p l))) (fun l _ => hε (p l))

/-- Triangle inequality removes bounded tuple weights after exact expansion.
No norm, injectivity, or positivity hypothesis is imposed on the phase values. -/
theorem weighted_moment_le_correlations {κ η : Type*} [Fintype κ]
    (D : Finset η) (s : ℕ) (ε : κ → ℂ) (z : κ → η → ℂ)
    (hε : ∀ b, ‖ε b‖ ≤ 1) :
    (∑ c ∈ D, ‖∑ b, ε b * z b c‖ ^ (2 * s)) ≤
      ∑ p : Fin s → κ, ∑ q : Fin s → κ,
        ‖∑ c ∈ D, (∏ l, z (p l) c) * conj (∏ l, z (q l) c)‖ := by
  classical
  let E (p : Fin s → κ) : ℂ := ∏ l, ε (p l)
  let C (p q : Fin s → κ) : ℂ :=
    ∑ c ∈ D, (∏ l, z (p l) c) * conj (∏ l, z (q l) c)
  have hE (p : Fin s → κ) : ‖E p‖ ≤ 1 := tuple_weight_norm_le s ε hε p
  have hEE (p q : Fin s → κ) : ‖E p * conj (E q)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_conj]
    exact (mul_le_mul (hE p) (hE q) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  have hnonneg : 0 ≤ ∑ c ∈ D, ‖∑ b, ε b * z b c‖ ^ (2 * s) :=
    Finset.sum_nonneg (fun c _ => pow_nonneg (norm_nonneg _) _)
  calc
    (∑ c ∈ D, ‖∑ b, ε b * z b c‖ ^ (2 * s)) =
        ‖((∑ c ∈ D, ‖∑ b, ε b * z b c‖ ^ (2 * s) : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ = ‖∑ p : Fin s → κ, ∑ q : Fin s → κ, (E p * conj (E q)) * C p q‖ :=
      congrArg norm (weighted_moment_expansion D s ε z)
    _ ≤ ∑ p : Fin s → κ, ‖∑ q : Fin s → κ, (E p * conj (E q)) * C p q‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p : Fin s → κ, ∑ q : Fin s → κ, ‖C p q‖ := by
      apply Finset.sum_le_sum
      intro p hp
      calc
        ‖∑ q : Fin s → κ, (E p * conj (E q)) * C p q‖ ≤
            ∑ q : Fin s → κ, ‖(E p * conj (E q)) * C p q‖ := norm_sum_le _ _
        _ ≤ ∑ q : Fin s → κ, ‖C p q‖ := by
          apply Finset.sum_le_sum
          intro q hq
          rw [norm_mul]
          exact (mul_le_mul_of_nonneg_right (hEE p q) (norm_nonneg _)).trans_eq (one_mul _)

end Item1WeightedMomentExpansion

run_cmd do
  for target in [``Item1WeightedMomentExpansion.norm_even_pow_complex,
      ``Item1WeightedMomentExpansion.weighted_sum_pow,
      ``Item1WeightedMomentExpansion.weighted_moment_expansion,
      ``Item1WeightedMomentExpansion.tuple_weight_norm_le,
      ``Item1WeightedMomentExpansion.weighted_moment_le_correlations] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "WEIGHTED MOMENT EXPANSION: 5 standard-axiom theorem guards passed."
