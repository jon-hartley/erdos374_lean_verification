import E374.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Choose.Factorization

/-!
# Mertens' first theorem (both directions, fully proved)

`S(n) = ∑_{p ≤ n} log p / p` satisfies `log n - C ≤ S(n) ≤ log n + log 4`.
Consequently, for `1 ≤ y ≤ z`, `∑_{y < p ≤ z} log p / p ≥ log z - log y - C'`.
The proof is the classical one through Legendre's formula for `log n!`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
set_option maxHeartbeats 1600000

noncomputable section
open scoped BigOperators
open Finset

namespace Erdos374.D35

/-- `log n = ∑_{p ∈ S} v_p(n) log p` for any finite `S` containing the prime factors of `n`. -/
theorem log_eq_sum_factorization {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ}
    (hS : n.primeFactors ⊆ S) :
    Real.log n = ∑ p ∈ S, (n.factorization p : ℝ) * Real.log p := by
  have h1 : (n : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p)) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    rw [Finsupp.prod, Nat.support_factorization]
    push_cast
    rfl
  rw [h1, Real.log_prod (fun p hp => by
    have := (Nat.prime_of_mem_primeFactors hp).pos
    positivity)]
  simp_rw [Real.log_pow]
  apply Finset.sum_subset hS
  intro p _ hp
  have : n.factorization p = 0 := by
    rw [← Nat.support_factorization] at hp
    exact Finsupp.notMem_support_iff.mp hp
  simp [this]

/-- Primes up to `n`. -/
def primesUpTo (n : ℕ) : Finset ℕ := (Finset.Ioc 0 n).filter Nat.Prime

theorem mem_primesUpTo {n p : ℕ} : p ∈ primesUpTo n ↔ p.Prime ∧ p ≤ n := by
  unfold primesUpTo
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨_, h⟩, hp⟩; exact ⟨hp, h⟩
  · rintro ⟨hp, h⟩; exact ⟨⟨hp.pos, h⟩, hp⟩

theorem primeFactors_factorial_subset (n : ℕ) : (n.factorial).primeFactors ⊆ primesUpTo n := by
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  rw [mem_primesUpTo]
  exact ⟨hpp, (Nat.Prime.dvd_factorial hpp).mp (Nat.dvd_of_mem_primeFactors hp)⟩

theorem log_factorial_eq (n : ℕ) :
    Real.log (n.factorial : ℝ) =
      ∑ p ∈ primesUpTo n, ((n.factorial).factorization p : ℝ) * Real.log p :=
  log_eq_sum_factorization (Nat.factorial_ne_zero n) (primeFactors_factorial_subset n)

theorem log_factorial_le (n : ℕ) : Real.log (n.factorial : ℝ) ≤ n * Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos n)
  exact_mod_cast Nat.factorial_le_pow n

theorem log_factorial_ge (n : ℕ) : n * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
  have h := Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hpos : (0 : ℝ) < (n : ℝ) ^ n / n.factorial := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have := Real.log_le_log hpos h
  rw [Real.log_exp, Real.log_div (by positivity) (by exact_mod_cast (Nat.factorial_ne_zero n)),
    Real.log_pow] at this
  linarith

theorem primesLE_eq_primesUpTo (n : ℕ) : Nat.primesLE n = primesUpTo n := by
  ext p
  rw [mem_primesUpTo, Nat.primesLE_eq_filter_range, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h1⟩

theorem theta_eq_sum_primesUpTo (n : ℕ) :
    Chebyshev.theta n = ∑ p ∈ primesUpTo n, Real.log p := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, primesLE_eq_primesUpTo]

/-- Chebyshev's bound in the form used here. -/
theorem sum_log_primesUpTo_le (n : ℕ) : ∑ p ∈ primesUpTo n, Real.log p ≤ Real.log 4 * n := by
  have h := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  rwa [theta_eq_sum_primesUpTo] at h

/-- Mertens sum `S(n) = ∑_{p ≤ n} log p / p`. -/
def mertensSum (n : ℕ) : ℝ := ∑ p ∈ primesUpTo n, Real.log p / p

/-- Upper Mertens bound: `S(n) ≤ log n + log 4`. -/
theorem mertensSum_le (n : ℕ) : mertensSum n ≤ Real.log n + Real.log 4 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [mertensSum, primesUpTo]
    positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  -- v_p(n!) ≥ n/p - 1
  have hv : ∀ p ∈ primesUpTo n,
      ((n : ℝ) / p - 1) * Real.log p ≤ ((n.factorial).factorization p : ℝ) * Real.log p := by
    intro p hp
    have hpp := (mem_primesUpTo.mp hp).1
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    apply mul_le_mul_of_nonneg_right _ hl
    have h1 : n / p ≤ (n.factorial).factorization p := by
      rw [Nat.factorization_factorial hpp (b := Nat.log p n + 2) (by omega)]
      have hmem : 1 ∈ Finset.Ico 1 (Nat.log p n + 2) := by simp
      have := Finset.single_le_sum (f := fun i => n / p ^ i) (fun i _ => Nat.zero_le _) hmem
      simpa using this
    have h2 : (n : ℝ) / p - 1 ≤ ((n / p : ℕ) : ℝ) := by
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hdm := Nat.div_add_mod n p
      have hmod := Nat.mod_lt n hpp.pos
      rw [div_sub_one hp0.ne', div_le_iff₀ hp0]
      have : (n : ℝ) = p * ((n / p : ℕ) : ℝ) + ((n % p : ℕ) : ℝ) := by
        exact_mod_cast hdm.symm
      have hm : ((n % p : ℕ) : ℝ) < p := by exact_mod_cast hmod
      nlinarith
    exact le_trans h2 (by exact_mod_cast h1)
  have hsum := Finset.sum_le_sum hv
  rw [← log_factorial_eq] at hsum
  have hsplit : ∑ p ∈ primesUpTo n, ((n : ℝ) / p - 1) * Real.log p =
      n * mertensSum n - ∑ p ∈ primesUpTo n, Real.log p := by
    unfold mertensSum
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (mem_primesUpTo.mp hp).1.ne_zero
    field_simp
  rw [hsplit] at hsum
  have hth := sum_log_primesUpTo_le n
  have hfl := log_factorial_le n
  have : n * mertensSum n ≤ n * (Real.log n + Real.log 4) := by nlinarith
  exact le_of_mul_le_mul_left this hnR

/-- The convergent correction `∑_p log p / (p (p-1))`, majorized termwise. -/
def corrTerm (k : ℕ) : ℝ := if 2 ≤ k then Real.log k / ((k : ℝ) * ((k : ℝ) - 1)) else 0

theorem corrTerm_nonneg (k : ℕ) : 0 ≤ corrTerm k := by
  unfold corrTerm
  split_ifs with h
  · have hk : (2 : ℝ) ≤ k := by exact_mod_cast h
    apply div_nonneg (Real.log_nonneg (by linarith))
    nlinarith
  · exact le_refl 0

theorem corrTerm_le (k : ℕ) : corrTerm k ≤ 4 * ((k : ℝ) ^ ((3 : ℝ) / 2))⁻¹ := by
  unfold corrTerm
  split_ifs with h
  · have hk : (2 : ℝ) ≤ k := by exact_mod_cast h
    have hk0 : (0 : ℝ) < k := by linarith
    have hlog : Real.log k ≤ (k : ℝ) ^ ((1 : ℝ) / 2) / (1 / 2) :=
      Real.log_le_rpow_div hk0.le (by norm_num)
    have hsplit : (k : ℝ) ^ ((3 : ℝ) / 2) = k * (k : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hk0, Real.rpow_one]
    have hs : 0 < (k : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hk0 _
    have hden : 0 < (k : ℝ) * ((k : ℝ) - 1) := by nlinarith
    rw [div_le_iff₀ hden, hsplit]
    have hkk : (k : ℝ) * ((k : ℝ) - 1) ≥ k * k / 2 := by nlinarith
    have hmain : 4 * (k * (k : ℝ) ^ ((1 : ℝ) / 2))⁻¹ * (k * (k - 1)) ≥
        2 * (k : ℝ) ^ ((1 : ℝ) / 2) := by
      have hsq : (k : ℝ) ^ ((1 : ℝ) / 2) * (k : ℝ) ^ ((1 : ℝ) / 2) = k := by
        rw [← Real.rpow_add hk0]; norm_num
      rw [ge_iff_le, ← sub_nonneg]
      have e : 4 * (k * (k : ℝ) ^ ((1 : ℝ) / 2))⁻¹ * (k * (k - 1)) - 2 * (k : ℝ) ^ ((1 : ℝ) / 2)
          = (2 * (k - 1) - k) * 2 / (k : ℝ) ^ ((1 : ℝ) / 2) := by
        field_simp
        nlinarith [hsq]
      rw [e]
      apply div_nonneg _ hs.le
      nlinarith
    linarith
  · positivity

theorem corrTerm_summable : Summable corrTerm := by
  have h : Summable (fun k : ℕ => 4 * ((k : ℝ) ^ ((3 : ℝ) / 2))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 4
  exact h.of_nonneg_of_le corrTerm_nonneg corrTerm_le

/-- The constant `C₃ = ∑_k corrTerm k`. -/
def corrConst : ℝ := ∑' k, corrTerm k

theorem sum_corr_le (n : ℕ) :
    ∑ p ∈ primesUpTo n, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ corrConst := by
  have h1 : ∑ p ∈ primesUpTo n, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) =
      ∑ p ∈ primesUpTo n, corrTerm p := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    unfold corrTerm
    rw [if_pos (mem_primesUpTo.mp hp).1.two_le]
  rw [h1]
  exact corrTerm_summable.sum_le_tsum _ (fun k _ => corrTerm_nonneg k)

/-- Lower Mertens bound: `S(n) ≥ log n - 1 - C₃`. -/
theorem mertensSum_ge (n : ℕ) : Real.log n - 1 - corrConst ≤ mertensSum n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : 0 ≤ corrConst := tsum_nonneg corrTerm_nonneg
    simp [mertensSum, primesUpTo]
    linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hv : ∀ p ∈ primesUpTo n,
      ((n.factorial).factorization p : ℝ) * Real.log p ≤
        ((n : ℝ) / p + n * (1 / ((p : ℝ) * ((p : ℝ) - 1)))) * Real.log p := by
    intro p hp
    have hpp := (mem_primesUpTo.mp hp).1
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    apply mul_le_mul_of_nonneg_right _ hl
    have h1 := Nat.factorization_factorial_le_div_pred hpp n
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have h2 : (((n / (p - 1) : ℕ)) : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) := by
      have := Nat.cast_div_le (α := ℝ) (m := n) (n := p - 1)
      rwa [Nat.cast_sub hpp.one_le, Nat.cast_one] at this
    have h3 : (n : ℝ) / ((p : ℝ) - 1) = (n : ℝ) / p + n * (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
      have hp0 : (p : ℝ) ≠ 0 := by linarith
      have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
      field_simp
      ring
    calc ((n.factorial).factorization p : ℝ) ≤ (((n / (p - 1) : ℕ)) : ℝ) := by exact_mod_cast h1
      _ ≤ _ := h2
      _ = _ := h3
  have hsum := Finset.sum_le_sum hv
  rw [← log_factorial_eq] at hsum
  have hsplit : ∑ p ∈ primesUpTo n,
      ((n : ℝ) / p + n * (1 / ((p : ℝ) * ((p : ℝ) - 1)))) * Real.log p =
      n * mertensSum n + n * ∑ p ∈ primesUpTo n, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
    unfold mertensSum
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primesUpTo.mp hp).1.two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  rw [hsplit] at hsum
  have hc := sum_corr_le n
  have hfl := log_factorial_ge n
  have : n * (Real.log n - 1 - corrConst) ≤ n * mertensSum n := by nlinarith
  exact le_of_mul_le_mul_left this hnR

/-- Interval form: `∑_{y < p ≤ z} log p / p ≥ log z - log y - C`. -/
theorem mertens_interval : ∃ C : ℝ, ∀ y z : ℕ, y ≤ z →
    Real.log z - Real.log y - C ≤
      ∑ p ∈ (Finset.Ioc y z).filter Nat.Prime, Real.log p / p := by
  refine ⟨1 + corrConst + Real.log 4, fun y z hyz => ?_⟩
  have hsplit : mertensSum z = mertensSum y +
      ∑ p ∈ (Finset.Ioc y z).filter Nat.Prime, Real.log p / p := by
    unfold mertensSum primesUpTo
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
    exact (Finset.sum_Ioc_consecutive _ (Nat.zero_le y) hyz).symm
  have h1 := mertensSum_ge z
  have h2 := mertensSum_le y
  linarith

end Erdos374.D35

end
