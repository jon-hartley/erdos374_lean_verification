import Item1TupleCollisionCounting

/-! An elementary zero-displacement majorant for ordered collisions.
Finite multiplicities retain all repeated values. No assumption of injectivity
or finiteness of the ambient additive group is made. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators Classical

namespace Item1DisplacedCollisionBound
open Item1TupleCollisionCounting

/-- A finite real sequence has autocorrelation at most its square sum. -/
theorem sum_mul_shift_le_sum_sq {η : Type*} [AddCommGroup η] [DecidableEq η]
    (A : Finset η) (n : η → ℝ) (hn : ∀ c, c ∉ A → n c = 0) (δ : η) :
    (∑ c ∈ A, n c*n (c-δ)) ≤ ∑ c ∈ A, (n c)^2 := by
  let B := A.image (fun c => c+δ)
  let K := A ∪ B
  have hprod : (∑ c ∈ K, n c*n (c-δ)) = ∑ c ∈ A, n c*n (c-δ) := by
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro c hc hnot
    rw [hn c hnot, zero_mul]
  have hsq : (∑ c ∈ K, (n c)^2) = ∑ c ∈ A, (n c)^2 := by
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro c hc hnot
    rw [hn c hnot, zero_pow (by decide : 2 ≠ 0)]
  have hshiftB : (∑ c ∈ K, (n (c-δ))^2) = ∑ c ∈ B, (n (c-δ))^2 := by
    symm
    apply Finset.sum_subset Finset.subset_union_right
    intro c hc hnot
    have hh : c-δ ∉ A := by
      intro h
      apply hnot
      exact Finset.mem_image.mpr ⟨c-δ, h, sub_add_cancel c δ⟩
    rw [hn (c-δ) hh, zero_pow (by decide : 2 ≠ 0)]
  have hshift : (∑ c ∈ K, (n (c-δ))^2) = ∑ c ∈ A, (n c)^2 := by
    rw [hshiftB]
    dsimp [B]
    rw [Finset.sum_image]
    · simp only [add_sub_cancel_right]
    · intro a ha b hb h
      exact add_right_cancel h
  have hpoint (c : η) : 2*(n c*n (c-δ)) ≤ (n c)^2+(n (c-δ))^2 := by
    nlinarith [sq_nonneg (n c-n (c-δ))]
  have hh := Finset.sum_le_sum (s := K) (fun c _ => hpoint c)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hprod, hsq, hshift] at hh
  linarith

/-- Multiplicity vanishes outside the finite image of the indexed family. -/
theorem fiberMultiplicity_eq_zero_of_not_mem {ι η : Type*}
    [Fintype ι] [DecidableEq η] (f : ι → η) (c : η)
    (hc : c ∉ frequencyImage f) : fiberMultiplicity f c = 0 := by
  unfold fiberMultiplicity
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have he := (Finset.mem_filter.mp hi).2
  apply hc
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, he⟩

/-- Every prescribed difference occurs at most as often as zero difference.
Both sides count ordered pairs, retaining repeated indexed frequencies. -/
theorem displaced_collision_le_zero {ι η : Type*} [Fintype ι]
    [AddCommGroup η] [DecidableEq η] (f : ι → η) (δ : η) :
    (∑ p, ∑ q, if f p-f q = δ then (1:ℝ) else 0) ≤
      ∑ p, ∑ q, if f p = f q then (1:ℝ) else 0 := by
  let n : η → ℝ := fun c => (fiberMultiplicity f c:ℝ)
  have hrow (p : ι) : (∑ q, if f p-f q = δ then (1:ℝ) else 0) = n (f p-δ) := by
    have he (q : ι) : f p-f q = δ ↔ f q = f p-δ := by
      rw [sub_eq_iff_comm]
      exact eq_comm
    simp only [he, n, fiberMultiplicity, Finset.sum_boole]
  simp_rw [hrow]
  rw [sum_grouped f (fun c => n (c-δ)), collisions_eq_sum_multiplicity_sq]
  change (∑ c ∈ frequencyImage f, n c*n (c-δ)) ≤
    ∑ c ∈ frequencyImage f, (n c)^2
  apply sum_mul_shift_le_sum_sq
  intro c hc
  simp only [n, fiberMultiplicity_eq_zero_of_not_mem f c hc, Nat.cast_zero]

end Item1DisplacedCollisionBound

run_cmd do
  for target in [``Item1DisplacedCollisionBound.sum_mul_shift_le_sum_sq,
      ``Item1DisplacedCollisionBound.fiberMultiplicity_eq_zero_of_not_mem,
      ``Item1DisplacedCollisionBound.displaced_collision_le_zero] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "DISPLACED COLLISION BOUND: 3 standard-axiom theorem guards passed."
