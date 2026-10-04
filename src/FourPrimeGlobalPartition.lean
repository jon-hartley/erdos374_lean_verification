import FourPrimePartitionProduct
import PolynomialLogEnvelope

/-!
Exact global doubling partitions of arbitrary finite supports in [2,X].
The index bound is logarithmic in X; its square is absorbed by any fixed
positive power selected before X and before both supports. No ratio
condition on either support is required.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Filter
open scoped BigOperators

namespace FourPrimeGlobalPartition
open FourPrimePartition

def k (X : ℝ) : ℕ := Nat.log 2 ⌊X⌋₊

theorem support_cover (X : ℝ) (hX : 1 ≤ X) (S : Finset ℕ)
    (hpos : ∀ n ∈ S, 2 ≤ n) (hupper : ∀ n ∈ S, (n : ℝ) ≤ X) :
    ∀ n ∈ S, 1 < n ∧ n ≤ scale 1 (k X + 1) := by
  intro n hn
  have hfloor : n ≤ ⌊X⌋₊ :=
    (Nat.le_floor_iff (by linarith : 0 ≤ X)).mpr (hupper n hn)
  have hpow := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊X⌋₊
  refine ⟨by have := hpos n hn; omega, ?_⟩
  simpa only [scale, mul_one, k] using (hfloor.trans_lt hpow).le

theorem biUnion_active_eq (X : ℝ) (hX : 1 ≤ X) (S : Finset ℕ)
    (hpos : ∀ n ∈ S, 2 ≤ n) (hupper : ∀ n ∈ S, (n : ℝ) ≤ X) :
    (active S 1 (k X)).biUnion (block S 1) = S :=
  FourPrimePartition.biUnion_active_eq S 1 (k X)
    (support_cover X hX S hpos hupper)

theorem sum_active_blocks {β : Type*} [AddCommMonoid β]
    (X : ℝ) (hX : 1 ≤ X) (S : Finset ℕ) (f : ℕ → β)
    (hpos : ∀ n ∈ S, 2 ≤ n) (hupper : ∀ n ∈ S, (n : ℝ) ≤ X) :
    (∑ j ∈ active S 1 (k X), ∑ n ∈ block S 1 j, f n) = ∑ n ∈ S, f n :=
  FourPrimePartition.sum_active_blocks S 1 (k X) f
    (support_cover X hX S hpos hupper)

theorem k_le_log (X : ℝ) (hX : 1 ≤ X) :
    (k X : ℝ) ≤ Real.log X / Real.log 2 := by
  have hX0 : 0 ≤ X := by linarith
  have hfloor : 1 ≤ ⌊X⌋₊ := (Nat.le_floor_iff hX0).mpr (by simpa using hX)
  have hpow : 2 ^ k X ≤ ⌊X⌋₊ := Nat.pow_log_le_self 2 (by omega)
  have hpowr : (2 : ℝ) ^ k X ≤ X := by
    calc
      _ = ((2 ^ k X : ℕ) : ℝ) := by norm_cast
      _ ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast hpow
      _ ≤ X := Nat.floor_le hX0
  have hlog := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ k X) hpowr
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hlog

theorem bin_count_le_log (X : ℝ) (hX : 1 ≤ X) :
    ((k X + 1 : ℕ) : ℝ) ≤ (1 + 1 / Real.log 2) * (1 + Real.log X) := by
  have hk := k_le_log X hX
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  have hi : 0 ≤ 1 / Real.log 2 :=
    (one_div_pos.mpr (Real.log_pos (by norm_num : (1 : ℝ) < 2))).le
  push_cast
  calc
    _ ≤ Real.log X / Real.log 2 + 1 := add_le_add hk le_rfl
    _ ≤ (1 + 1 / Real.log 2) * (1 + Real.log X) := by
      rw [div_eq_mul_inv, one_div] at *
      nlinarith

theorem family_card_le_square (X : ℝ) (S T : Finset ℕ) :
    (family S T 1 1 (k X) (k X)).card ≤ (k X + 1) ^ 2 := by
  simpa only [pow_two] using family_card_le S T 1 1 (k X) (k X)

theorem eventually_family_cost (c : ℝ) (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧ ((k X + 1 : ℕ) : ℝ) ^ 2 ≤ X ^ (c / 2) := by
  filter_upwards [PolynomialLogEnvelope.eventually_bound
    ((1 + 1 / Real.log 2) ^ 2) 2 (c / 2) (sq_nonneg _) (by positivity)]
    with X hbound
  refine ⟨hbound.1, ?_⟩
  have hcount := bin_count_le_log X hbound.1
  calc
    _ ≤ ((1 + 1 / Real.log 2) * (1 + Real.log X)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hcount 2
    _ = (1 + 1 / Real.log 2) ^ 2 * (1 + Real.log X) ^ 2 := mul_pow _ _ _
    _ ≤ X ^ (c / 2) := hbound.2

theorem eventually_all_family_cost (c : ℝ) (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧ ∀ S T : Finset ℕ,
      ((family S T 1 1 (k X) (k X)).card : ℝ) ≤ X ^ (c / 2) := by
  filter_upwards [eventually_family_cost c hc] with X hh
  refine ⟨hh.1, ?_⟩
  intro S T
  apply le_trans _ hh.2
  exact_mod_cast family_card_le_square X S T

end FourPrimeGlobalPartition

#print axioms FourPrimeGlobalPartition.eventually_family_cost
run_cmd do
  for target in [``FourPrimeGlobalPartition.support_cover,
      ``FourPrimeGlobalPartition.biUnion_active_eq,
      ``FourPrimeGlobalPartition.sum_active_blocks,
      ``FourPrimeGlobalPartition.k_le_log,
      ``FourPrimeGlobalPartition.bin_count_le_log,
      ``FourPrimeGlobalPartition.family_card_le_square,
      ``FourPrimeGlobalPartition.eventually_family_cost,
      ``FourPrimeGlobalPartition.eventually_all_family_cost] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "FOUR PRIME GLOBAL PARTITION PASSED"
