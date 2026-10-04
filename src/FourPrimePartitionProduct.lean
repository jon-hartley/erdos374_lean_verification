import FourPrimePartition

/-! Cartesian products of the exact support partitions. All original
coefficients, including multiplicities already collected into them, are retained. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace FourPrimePartition

def family (S T : Finset ℕ) (a b k l : ℕ) : Finset (ℕ × ℕ) :=
  active S a k ×ˢ active T b l

theorem family_card_le (S T : Finset ℕ) (a b k l : ℕ) :
    (family S T a b k l).card ≤ (k+1)*(l+1) := by
  rw [family, Finset.card_product]
  exact Nat.mul_le_mul (active_card_le S a k) (active_card_le T b l)

theorem family_card_le_ten (S T : Finset ℕ) (a b : ℕ) :
    (family S T a b 4 1).card ≤ 10 := family_card_le S T a b 4 1

theorem family_blocks_nonempty (S T : Finset ℕ) (a b k l : ℕ)
    (ij : ℕ × ℕ) (hij : ij ∈ family S T a b k l) :
    (block S a ij.1).Nonempty ∧ (block T b ij.2).Nonempty := by
  have hi := Finset.mem_product.mp hij
  exact ⟨active_nonempty_block S a k ij.1 hi.1,
    active_nonempty_block T b l ij.2 hi.2⟩

/-- The exact product sum is preserved for an arbitrary summand, so this
also applies to coefficients times a divisor remainder at every real x. -/
theorem sum_family_blocks {β : Type*} [AddCommMonoid β]
    (S T : Finset ℕ) (a b k l : ℕ) (f : ℕ → ℕ → β)
    (hS : ∀ n ∈ S, a < n ∧ n ≤ scale a (k+1))
    (hT : ∀ n ∈ T, b < n ∧ n ≤ scale b (l+1)) :
    (∑ ij ∈ family S T a b k l,
      ∑ m ∈ block S a ij.1, ∑ n ∈ block T b ij.2, f m n) =
      ∑ m ∈ S, ∑ n ∈ T, f m n := by
  calc
    _ = ∑ i ∈ active S a k, ∑ m ∈ block S a i,
        ∑ j ∈ active T b l, ∑ n ∈ block T b j, f m n := by
      rw [family, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm (s := active T b l) (t := block S a i)
        (f := fun j m => ∑ n ∈ block T b j, f m n)
    _ = ∑ i ∈ active S a k, ∑ m ∈ block S a i,
        ∑ n ∈ T, f m n := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro m hm
      exact sum_active_blocks T b l (f m) hT
    _ = _ := sum_active_blocks S a k (fun m => ∑ n ∈ T, f m n) hS

/-- Any actual member of an active bin transfers lower support bounds to
half the bin length. This keeps the integer endpoint used by later analysis. -/
theorem active_scale_lower (S : Finset ℕ) (a k j : ℕ) (L : ℝ)
    (hL : ∀ n ∈ S, L ≤ (n:ℝ)) (hj : j ∈ active S a k) :
    L/2 ≤ (scale a j:ℝ) := by
  obtain ⟨n, hn⟩ := active_nonempty_block S a k j hj
  have hb := (mem_block S a j n).mp hn
  have hu : (n:ℝ) ≤ 2*(scale a j:ℝ) := by exact_mod_cast hb.2.2
  linarith [hL n hb.1]

theorem active_scale_lt_upper (S : Finset ℕ) (a k j : ℕ) (U : ℝ)
    (hU : ∀ n ∈ S, (n:ℝ) ≤ U) (hj : j ∈ active S a k) :
    (scale a j:ℝ) < U := by
  obtain ⟨n, hn⟩ := active_nonempty_block S a k j hj
  have hb := (mem_block S a j n).mp hn
  have hl : (scale a j:ℝ) < (n:ℝ) := by exact_mod_cast hb.2.1
  exact hl.trans_le (hU n hb.1)

/-- Independent supports let a pair of nonempty bins inherit the original
product upper bound by choosing one actual member in each bin. -/
theorem family_scale_product_lt (S T : Finset ℕ) (a b k l : ℕ)
    (U : ℝ) (_ha : 1 ≤ a) (hb : 1 ≤ b)
    (hU : ∀ m ∈ S, ∀ n ∈ T, (m:ℝ)*(n:ℝ) ≤ U)
    (ij : ℕ × ℕ) (hij : ij ∈ family S T a b k l) :
    (scale a ij.1:ℝ)*(scale b ij.2:ℝ) < U := by
  obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := family_blocks_nonempty S T a b k l ij hij
  have hm' := (mem_block S a ij.1 m).mp hm
  have hn' := (mem_block T b ij.2 n).mp hn
  have hmlo : (scale a ij.1:ℝ) < (m:ℝ) := by exact_mod_cast hm'.2.1
  have hnlo : (scale b ij.2:ℝ) < (n:ℝ) := by exact_mod_cast hn'.2.1
  have hbpos : (0:ℝ) < scale b ij.2 := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) (scale_pos b ij.2 hb))
  exact (mul_lt_mul hmlo hnlo.le hbpos (by positivity)).trans_le (hU m hm'.1 n hn'.1)

#print axioms sum_family_blocks
#print axioms family_scale_product_lt
run_cmd do
  for target in [``family_card_le, ``family_card_le_ten, ``family_blocks_nonempty,
      ``sum_family_blocks, ``active_scale_lower, ``active_scale_lt_upper,
      ``family_scale_product_lt] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "FOUR_PRIME_PARTITION_PRODUCT_PASSED"

end FourPrimePartition
end
