import SieveProfileMass
import SieveCollisionBounds

/-! Repeated-band mass of actual ordered profiles. Removing two equal entries
is injective on a sorted family, so the bound has no factor from the allowed
profile length. All coordinate multiplicities remain literal. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace SieveProfileCollision

def erasePair (i : ℕ) (t : List ℕ) : List ℕ := (t.erase i).erase i

theorem erasePair_sublist (i : ℕ) (t : List ℕ) : (erasePair i t).Sublist t :=
  List.erase_sublist.trans List.erase_sublist

theorem perm_pair_erasePair (i : ℕ) (t : List ℕ) (hi : 2 ≤ t.count i) :
    t.Perm (i :: i :: erasePair i t) := by
  have hm : i ∈ t := List.count_pos_iff.mp (by omega)
  have hm' : i ∈ t.erase i := by
    apply List.count_pos_iff.mp
    rw [List.count_erase_self]
    omega
  exact (List.perm_cons_erase hm).trans ((List.perm_cons_erase hm').cons i)

theorem erasePair_injective_sorted (i : ℕ) (t v : List ℕ)
    (ht : t.Pairwise (· ≥ ·)) (hv : v.Pairwise (· ≥ ·))
    (hti : 2 ≤ t.count i) (hvi : 2 ≤ v.count i)
    (he : erasePair i t = erasePair i v) : t = v := by
  have hp := perm_pair_erasePair i t hti
  rw [he] at hp
  exact (hp.trans (perm_pair_erasePair i v hvi).symm).eq_of_pairwise' ht hv

theorem product_erasePair (i : ℕ) (t : List ℕ) (w : ℕ → ℝ)
    (hi : 2 ≤ t.count i) :
    (t.map w).prod = w i ^ 2 * ((erasePair i t).map w).prod := by
  have h := ((perm_pair_erasePair i t hi).map w).prod_eq
  simpa only [List.map_cons, List.prod_cons, pow_two, mul_assoc] using h

theorem profile_product_nonneg (t : List ℕ) (m : ℕ) (w : ℕ → ℝ)
    (hr : ∀ i ∈ t, i < m) (hw : ∀ i < m, 0 ≤ w i) : 0 ≤ (t.map w).prod := by
  apply List.prod_nonneg
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact hw i (hr i hi)

theorem repeated_at_mass_le_product (A : Finset (List ℕ)) (m K i : ℕ)
    (w : ℕ → ℝ) (hlen : ∀ t ∈ A, t.length ≤ K)
    (hr : ∀ t ∈ A, ∀ j ∈ t, j < m)
    (ho : ∀ t ∈ A, t.Pairwise (· ≥ ·))
    (hrep : ∀ t ∈ A, 2 ≤ t.count i)
    (hw : ∀ j < m, 0 ≤ w j) (hw1 : ∀ j < m, w j < 1) :
    (∑ t ∈ A, (t.map w).prod) ≤
      w i ^ 2 * ∏ j : Fin m, 1/(1-w j.val) := by
  classical
  have hinj : Set.InjOn (erasePair i) (↑A : Set (List ℕ)) := by
    intro t ht v hv he
    exact erasePair_injective_sorted i t v (ho t ht) (ho v hv)
      (hrep t ht) (hrep v hv) he
  have hdata : ∀ v ∈ A.image (erasePair i),
      v.length ≤ K ∧ (∀ j ∈ v, j < m) ∧ v.Pairwise (· ≥ ·) := by
    intro v hv
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
    have hs := erasePair_sublist i t
    exact ⟨hs.length_le.trans (hlen t ht), fun j hj => hr t ht j (hs.subset hj),
      (ho t ht).sublist hs⟩
  calc
    _ = w i ^ 2 * ∑ v ∈ A.image (erasePair i), (v.map w).prod := by
      rw [Finset.sum_image hinj, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun t ht => product_erasePair i t w (hrep t ht))
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (SieveProfileMass.sorted_mass_le_product _ m K w
        (fun v hv => (hdata v hv).1) (fun v hv => (hdata v hv).2.1)
        (fun v hv => (hdata v hv).2.2) hw hw1) (sq_nonneg _)

/-- A union bound over the repeated value, not over all pairs of positions. -/
theorem repeated_mass_le_product (A : Finset (List ℕ)) (m K : ℕ) (w : ℕ → ℝ)
    (hlen : ∀ t ∈ A, t.length ≤ K) (hr : ∀ t ∈ A, ∀ i ∈ t, i < m)
    (ho : ∀ t ∈ A, t.Pairwise (· ≥ ·)) (hrep : ∀ t ∈ A, ¬t.Nodup)
    (hw : ∀ i < m, 0 ≤ w i) (hw1 : ∀ i < m, w i < 1) :
    (∑ t ∈ A, (t.map w).prod) ≤
      (∑ i ∈ Finset.range m, w i ^ 2) * ∏ i : Fin m, 1/(1-w i.val) := by
  classical
  have hpoint : ∀ t ∈ A, (t.map w).prod ≤
      ∑ i ∈ Finset.range m, if 2 ≤ t.count i then (t.map w).prod else 0 := by
    intro t ht
    obtain ⟨i, hi⟩ : ∃ i, 2 ≤ t.count i := by
      by_contra hn
      apply hrep t ht
      apply List.nodup_iff_count_le_one.mpr
      intro i
      have hh : ¬2 ≤ t.count i := fun h => hn ⟨i, h⟩
      omega
    have him : i ∈ t := List.count_pos_iff.mp (by omega)
    have hn := profile_product_nonneg t m w (hr t ht) hw
    have hb := Finset.single_le_sum
      (s := Finset.range m) (f := fun j => if 2 ≤ t.count j then (t.map w).prod else 0)
      (fun j _ => by split_ifs <;> positivity) (Finset.mem_range.mpr (hr t ht i him))
    simpa only [ite_eq_left hi] using hb
  calc
    _ ≤ ∑ t ∈ A, ∑ i ∈ Finset.range m,
        if 2 ≤ t.count i then (t.map w).prod else 0 := Finset.sum_le_sum hpoint
    _ = ∑ i ∈ Finset.range m, ∑ t ∈ A.filter (fun t => 2 ≤ t.count i),
        (t.map w).prod := by rw [Finset.sum_comm]; simp only [Finset.sum_filter]
    _ ≤ ∑ i ∈ Finset.range m, w i ^ 2 * ∏ j : Fin m, 1/(1-w j.val) := by
      apply Finset.sum_le_sum
      intro i _
      exact repeated_at_mass_le_product _ m K i w
        (fun t ht => hlen t (Finset.mem_filter.mp ht).1)
        (fun t ht => hr t (Finset.mem_filter.mp ht).1)
        (fun t ht => ho t (Finset.mem_filter.mp ht).1)
        (fun t ht => (Finset.mem_filter.mp ht).2) hw hw1
    _ = _ := (Finset.sum_mul ..).symm

theorem repeated_mass_le_exp (A : Finset (List ℕ)) (m K : ℕ) (w : ℕ → ℝ)
    (hlen : ∀ t ∈ A, t.length ≤ K) (hr : ∀ t ∈ A, ∀ i ∈ t, i < m)
    (ho : ∀ t ∈ A, t.Pairwise (· ≥ ·)) (hrep : ∀ t ∈ A, ¬t.Nodup)
    (hw : ∀ i < m, 0 ≤ w i) (hw2 : ∀ i < m, w i ≤ 1/2) :
    (∑ t ∈ A, (t.map w).prod) ≤
      (∑ i ∈ Finset.range m, w i ^ 2) * Real.exp (2 * ∑ i ∈ Finset.range m, w i) := by
  have hp : (∏ i : Fin m, 1/(1-w i.val)) ≤
      Real.exp (2 * ∑ i ∈ Finset.range m, w i) := by
    calc
      _ ≤ ∏ i : Fin m, Real.exp (2*w i.val) := by
        apply Finset.prod_le_prod₀
        · intro i _
          exact div_nonneg zero_le_one (by linarith [hw2 i.val i.isLt])
        · intro i _
          exact SieveProfileMass.inverse_le_exp _ (hw i.val i.isLt) (hw2 i.val i.isLt)
      _ = _ := by rw [← Real.exp_sum, ← Finset.mul_sum, Fin.sum_univ_eq_sum_range]
  exact (repeated_mass_le_product A m K w hlen hr ho hrep hw
    (fun i hi => (hw2 i hi).trans_lt (by norm_num))).trans
    (mul_le_mul_of_nonneg_left hp (Finset.sum_nonneg (fun i _ => sq_nonneg _)))

/-- A bound by the maximum actual band mass times total actual band mass. -/
theorem repeated_mass_le_max_exp (A : Finset (List ℕ)) (m K : ℕ) (w : ℕ → ℝ)
    (η : ℝ) (hlen : ∀ t ∈ A, t.length ≤ K) (hr : ∀ t ∈ A, ∀ i ∈ t, i < m)
    (ho : ∀ t ∈ A, t.Pairwise (· ≥ ·)) (hrep : ∀ t ∈ A, ¬t.Nodup)
    (hw : ∀ i < m, 0 ≤ w i) (hw2 : ∀ i < m, w i ≤ 1/2)
    (hη : ∀ i < m, w i ≤ η) :
    (∑ t ∈ A, (t.map w).prod) ≤
      (η * ∑ i ∈ Finset.range m, w i) * Real.exp (2 * ∑ i ∈ Finset.range m, w i) := by
  apply (repeated_mass_le_exp A m K w hlen hr ho hrep hw hw2).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [pow_two]
  exact mul_le_mul_of_nonneg_right (hη i (Finset.mem_range.mp hi))
    (hw i (Finset.mem_range.mp hi))

theorem strict_iff_nodup_of_sorted (t : List ℕ) (ht : t.Pairwise (· ≥ ·)) :
    t.Pairwise (· > ·) ↔ t.Nodup := by
  constructor
  · intro hs
    exact List.nodup_iff_pairwise_ne.mpr (hs.imp (fun h => ne_of_gt h))
  · intro hn
    exact (ht.and (List.nodup_iff_pairwise_ne.mp hn)).imp
      (fun h => lt_of_le_of_ne h.1 (Ne.symm h.2))

/-- Within any actual weakly ordered finite family, the exact difference from
its strictly ordered subfamily is the mass of profiles with a repeated band. -/
theorem weak_sub_strict_eq_repeated (A : Finset (List ℕ)) (w : ℕ → ℝ)
    (ho : ∀ t ∈ A, t.Pairwise (· ≥ ·)) :
    (∑ t ∈ A, (t.map w).prod) -
        (∑ t ∈ A.filter (fun t => t.Pairwise (· > ·)), (t.map w).prod) =
      ∑ t ∈ A.filter (fun t => ¬t.Nodup), (t.map w).prod := by
  classical
  have he : A.filter (fun t => t.Pairwise (· > ·)) = A.filter List.Nodup := by
    ext t
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ht, hs⟩
      exact ⟨ht, (strict_iff_nodup_of_sorted t (ho t ht)).mp hs⟩
    · rintro ⟨ht, hn⟩
      exact ⟨ht, (strict_iff_nodup_of_sorted t (ho t ht)).mpr hn⟩
  rw [he]
  have h := Finset.sum_filter_add_sum_filter_not A List.Nodup (fun t => (t.map w).prod)
  linarith

theorem weak_sub_strict_bounds (A : Finset (List ℕ)) (m K : ℕ) (w : ℕ → ℝ)
    (hlen : ∀ t ∈ A, t.length ≤ K) (hr : ∀ t ∈ A, ∀ i ∈ t, i < m)
    (ho : ∀ t ∈ A, t.Pairwise (· ≥ ·))
    (hw : ∀ i < m, 0 ≤ w i) (hw1 : ∀ i < m, w i < 1) :
    let E := (∑ t ∈ A, (t.map w).prod) -
      ∑ t ∈ A.filter (fun t => t.Pairwise (· > ·)), (t.map w).prod
    0 ≤ E ∧ E ≤ (∑ i ∈ Finset.range m, w i ^ 2) *
      ∏ i : Fin m, 1/(1-w i.val) := by
  classical
  dsimp only
  rw [weak_sub_strict_eq_repeated A w ho]
  constructor
  · exact Finset.sum_nonneg (fun t ht =>
      profile_product_nonneg t m w (hr t (Finset.mem_filter.mp ht).1) hw)
  · exact repeated_mass_le_product _ m K w
      (fun t ht => hlen t (Finset.mem_filter.mp ht).1)
      (fun t ht => hr t (Finset.mem_filter.mp ht).1)
      (fun t ht => ho t (Finset.mem_filter.mp ht).1)
      (fun t ht => (Finset.mem_filter.mp ht).2) hw hw1

#print axioms repeated_mass_le_product
#print axioms repeated_mass_le_max_exp
run_cmd do
  for decl in [``erasePair_sublist, ``perm_pair_erasePair, ``erasePair_injective_sorted,
      ``product_erasePair, ``profile_product_nonneg, ``repeated_at_mass_le_product,
      ``repeated_mass_le_product, ``repeated_mass_le_exp, ``repeated_mass_le_max_exp,
      ``strict_iff_nodup_of_sorted, ``weak_sub_strict_eq_repeated,
      ``weak_sub_strict_bounds] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "SIEVE PROFILE COLLISION PASSED; standard axioms only"

end SieveProfileCollision
end
