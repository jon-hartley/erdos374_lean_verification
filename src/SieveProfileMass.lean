import SieveBoxGrouping
import SieveSignedComparison
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum

/-! Quantitative unsigned mass for ordered box profiles. Repeated indices
are encoded by their multiplicities, not by all permutations. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators

namespace SieveProfileMass

def counts (m K : ℕ) (t : List ℕ) : Fin m → Fin (K+1) :=
  fun i => ⟨min (t.count i.val) K, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

theorem counts_val (m K : ℕ) (t : List ℕ) (ht : t.length ≤ K) (i : Fin m) :
    (counts m K t i).val = t.count i.val := by
  exact Nat.min_eq_left (List.count_le_length.trans ht)

theorem counts_injective_sorted (m K : ℕ) (t v : List ℕ)
    (ht : t.length ≤ K) (hv : v.length ≤ K)
    (htr : ∀ i ∈ t, i < m) (hvr : ∀ i ∈ v, i < m)
    (hto : t.Pairwise (· ≥ ·)) (hvo : v.Pairwise (· ≥ ·))
    (he : counts m K t = counts m K v) : t = v := by
  have hp : t.Perm v := by
    apply List.perm_iff_count.mpr
    intro i
    by_cases hi : i < m
    · have hh := congrArg (fun c => (c ⟨i, hi⟩).val) he
      simpa only [counts_val m K t ht, counts_val m K v hv] using hh
    · have hit : i ∉ t := fun h => hi (htr i h)
      have hiv : i ∉ v := fun h => hi (hvr i h)
      simp [List.count_eq_zero_of_not_mem hit, List.count_eq_zero_of_not_mem hiv]
  exact hp.eq_of_pairwise' hto hvo

theorem product_eq_counts (m K : ℕ) (t : List ℕ) (w : ℕ → ℝ)
    (ht : t.length ≤ K) (hr : ∀ i ∈ t, i < m) :
    (t.map w).prod = ∏ i : Fin m, w i.val ^ (counts m K t i).val := by
  simp only [counts_val m K t ht]
  rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => w i ^ t.count i),
    Finset.prod_list_map_count]
  apply Finset.prod_subset
  · intro i hi
    exact Finset.mem_range.mpr (hr i (List.mem_toFinset.mp hi))
  · intro i _ hi
    have hn : i ∉ t := by simpa using hi
    simp [List.count_eq_zero_of_not_mem hn]

theorem geometric_le (w : ℝ) (hw : 0 ≤ w) (hw1 : w < 1) (n : ℕ) :
    (∑ k ∈ Finset.range n, w^k) ≤ 1/(1-w) := by
  apply (le_div_iff₀ (sub_pos.mpr hw1)).mpr
  rw [geom_sum_mul_neg]
  exact sub_le_self _ (pow_nonneg hw n)

theorem inverse_le_exp (w : ℝ) (hw : 0 ≤ w) (hw2 : w ≤ 1/2) :
    1/(1-w) ≤ Real.exp (2*w) := by
  have hpos : 0 < 1-w := by linarith
  have hrat : 1/(1-w) ≤ 1+2*w := by
    apply (div_le_iff₀ hpos).mpr
    nlinarith [mul_nonneg hw (show 0 ≤ 1-2*w by linarith)]
  exact hrat.trans (by simpa only [add_comm] using Real.add_one_le_exp (2*w))

theorem sorted_mass_le_product (A : Finset (List ℕ)) (m K : ℕ) (w : ℕ → ℝ)
    (hlen : ∀ t ∈ A, t.length ≤ K) (hr : ∀ t ∈ A, ∀ i ∈ t, i < m)
    (ho : ∀ t ∈ A, t.Pairwise (· ≥ ·)) (hw : ∀ i < m, 0 ≤ w i)
    (hw1 : ∀ i < m, w i < 1) :
    (∑ t ∈ A, (t.map w).prod) ≤ ∏ i : Fin m, 1/(1-w i.val) := by
  classical
  have hc : Set.InjOn (counts m K) (↑A : Set (List ℕ)) := by
    intro t ht v hv he
    exact counts_injective_sorted m K t v (hlen t ht) (hlen v hv)
      (hr t ht) (hr v hv) (ho t ht) (ho v hv) he
  have hsum := SieveSignedComparison.sum_le_of_injection A Finset.univ (counts m K)
    (fun t => (t.map w).prod) (fun c : Fin m → Fin (K+1) => ∏ i : Fin m, w i.val ^ (c i).val)
    (fun _ _ => Finset.mem_univ _) hc
    (fun t ht => product_eq_counts m K t w (hlen t ht) (hr t ht))
    (fun c _ => Finset.prod_nonneg (fun i _ => pow_nonneg (hw i.val i.isLt) _))
  calc
    _ ≤ ∑ c : Fin m → Fin (K+1), ∏ i : Fin m, w i.val ^ (c i).val := hsum
    _ = ∏ i : Fin m, ∑ k : Fin (K+1), w i.val ^ k.val :=
      (Fintype.prod_sum (fun (i : Fin m) (k : Fin (K+1)) => w i.val ^ k.val)).symm
    _ ≤ _ := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Finset.sum_nonneg (fun k _ => pow_nonneg (hw i.val i.isLt) _)
      · intro i _
        rw [Fin.sum_univ_eq_sum_range]
        exact geometric_le (w i.val) (hw i.val i.isLt) (hw1 i.val i.isLt) (K+1)

/-- The bound is independent of the allowed sequence length. This preserves
the ordered-profile advantage needed when K grows like s⁻². -/
theorem sorted_mass_le_exp (A : Finset (List ℕ)) (m K : ℕ) (w : ℕ → ℝ)
    (hlen : ∀ t ∈ A, t.length ≤ K) (hr : ∀ t ∈ A, ∀ i ∈ t, i < m)
    (ho : ∀ t ∈ A, t.Pairwise (· ≥ ·)) (hw : ∀ i < m, 0 ≤ w i)
    (hw2 : ∀ i < m, w i ≤ 1/2) :
    (∑ t ∈ A, (t.map w).prod) ≤ Real.exp (2 * ∑ i ∈ Finset.range m, w i) := by
  calc
    _ ≤ ∏ i : Fin m, 1/(1-w i.val) := sorted_mass_le_product A m K w hlen hr ho hw
      (fun i hi => (hw2 i hi).trans_lt (by norm_num))
    _ ≤ ∏ i : Fin m, Real.exp (2*w i.val) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact div_nonneg zero_le_one (by linarith [hw2 i.val i.isLt])
      · intro i _
        exact inverse_le_exp _ (hw i.val i.isLt) (hw2 i.val i.isLt)
    _ = _ := by
      rw [← Real.exp_sum, ← Finset.mul_sum, Fin.sum_univ_eq_sum_range]

#print axioms sorted_mass_le_exp
run_cmd do
  for decl in [``counts_val, ``counts_injective_sorted, ``product_eq_counts,
    ``geometric_le, ``inverse_le_exp, ``sorted_mass_le_product, ``sorted_mass_le_exp] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end SieveProfileMass
end
