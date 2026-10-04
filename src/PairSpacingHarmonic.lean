import SingletonHarmonic
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace Erdos374.PairSpacingHarmonic

def H (N : ℕ) : ℝ := ∑ k ∈ Finset.range N, 1 / (k + 1 : ℝ)

theorem H_eq_harmonic (N : ℕ) : H N = (harmonic N : ℝ) := by
  simp [H, harmonic, Rat.cast_sum, Rat.cast_inv, one_div]

theorem H_eq_harmonicSum (N : ℕ) : H N = SingletonHarmonic.harmonicSum N := by
  rw [H_eq_harmonic]
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
    SingletonHarmonic.harmonicSum, one_div]

theorem H_nonneg (N : ℕ) : 0 ≤ H N := by
  exact Finset.sum_nonneg fun k _ => by positivity

theorem ordered_gap {N : ℕ} (f : Fin N → ℝ) (δ : ℝ)
    (hf : StrictMono f)
    (hsep : ∀ i j, i ≠ j → δ ≤ |f i - f j|)
    {i j : Fin N} (hij : i ≤ j) :
    δ * ((j : ℝ) - (i : ℝ)) ≤ f j - f i := by
  have hm : Monotone (fun k : Fin N => f k - δ * (k : ℝ)) := by
    cases N with
    | zero => exact fun a => Fin.elim0 a
    | succ N =>
      apply Fin.monotone_iff_le_succ.mpr
      intro k
      have hk : k.castSucc < k.succ := by exact_mod_cast Nat.lt_succ_self k.val
      have hh := hsep k.succ k.castSucc (ne_of_gt hk)
      rw [abs_of_pos (sub_pos.mpr (hf hk))] at hh
      simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one] at hh ⊢
      linarith
  have hh := hm hij
  linarith

theorem lower_reciprocal_sum_le {N : ℕ} (i : Fin N) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin N => j < i),
      1 / ((i.val - j.val : ℕ) : ℝ)) ≤ H N := by
  let s := Finset.univ.filter (fun j : Fin N => j < i)
  let g := fun j : Fin N => i.val - j.val - 1
  have hg : Set.InjOn g (s : Set (Fin N)) := by
    intro a ha b hb hab
    have ha' : a.val < i.val := (Finset.mem_filter.mp ha).2
    have hb' : b.val < i.val := (Finset.mem_filter.mp hb).2
    apply Fin.ext
    dsimp [g] at hab
    omega
  have hsub : s.image g ⊆ Finset.range N := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨j, hj, rfl⟩
    exact Finset.mem_range.mpr (by dsimp [g]; omega)
  have heq : (∑ j ∈ s, 1 / ((i.val - j.val : ℕ) : ℝ)) =
      ∑ k ∈ s.image g, 1 / (k + 1 : ℝ) := by
    rw [Finset.sum_image hg]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j.val < i.val := (Finset.mem_filter.mp hj).2
    have hnat : g j + 1 = i.val - j.val := by dsimp [g]; omega
    rw [← Nat.cast_add_one, hnat]
  change (∑ j ∈ s, _) ≤ _
  rw [heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

theorem upper_reciprocal_sum_le {N : ℕ} (i : Fin N) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j),
      1 / ((j.val - i.val : ℕ) : ℝ)) ≤ H N := by
  let s := Finset.univ.filter (fun j : Fin N => i < j)
  let g := fun j : Fin N => j.val - i.val - 1
  have hg : Set.InjOn g (s : Set (Fin N)) := by
    intro a ha b hb hab
    have ha' : i.val < a.val := (Finset.mem_filter.mp ha).2
    have hb' : i.val < b.val := (Finset.mem_filter.mp hb).2
    apply Fin.ext
    dsimp [g] at hab
    omega
  have hsub : s.image g ⊆ Finset.range N := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨j, hj, rfl⟩
    exact Finset.mem_range.mpr (by dsimp [g]; omega)
  have heq : (∑ j ∈ s, 1 / ((j.val - i.val : ℕ) : ℝ)) =
      ∑ k ∈ s.image g, 1 / (k + 1 : ℝ) := by
    rw [Finset.sum_image hg]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : i.val < j.val := (Finset.mem_filter.mp hj).2
    have hnat : g j + 1 = j.val - i.val := by dsimp [g]; omega
    rw [← Nat.cast_add_one, hnat]
  change (∑ j ∈ s, _) ≤ _
  rw [heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

theorem ordered_row_le {N : ℕ} (f : Fin N → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hf : StrictMono f)
    (hsep : ∀ i j, i ≠ j → δ ≤ |f i - f j|) (i : Fin N) :
    (∑ j ∈ Finset.univ.erase i, 1 / |f i - f j|) ≤ 2 * H N / δ := by
  let lo := Finset.univ.filter (fun j : Fin N => j < i)
  let hi := Finset.univ.filter (fun j : Fin N => i < j)
  have hsplit : Finset.univ.erase i = lo ∪ hi := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_univ, and_true,
      Finset.mem_union, Finset.mem_filter, true_and, lo, hi]
    exact ne_iff_lt_or_gt
  have hdisj : Disjoint lo hi := by
    apply Finset.disjoint_left.mpr
    intro j hjlo hjhi
    exact (not_lt_of_gt (Finset.mem_filter.mp hjlo).2) (Finset.mem_filter.mp hjhi).2
  have hlo : (∑ j ∈ lo, 1 / |f i - f j|) ≤ H N / δ := by
    calc
      _ ≤ ∑ j ∈ lo, (1 / ((i.val - j.val : ℕ) : ℝ)) / δ := by
        apply Finset.sum_le_sum
        intro j hj
        have hji : j < i := (Finset.mem_filter.mp hj).2
        have hg := ordered_gap f δ hf hsep hji.le
        have hc : ((i.val - j.val : ℕ) : ℝ) = (i : ℝ) - (j : ℝ) :=
          Nat.cast_sub hji.le
        rw [abs_of_pos (sub_pos.mpr (hf hji))]
        rw [hc]
        have hp : 0 < (i : ℝ) - (j : ℝ) :=
          sub_pos.mpr (by exact_mod_cast hji)
        calc
          1 / (f i - f j) ≤ 1 / (δ * ((i : ℝ) - (j : ℝ))) :=
            one_div_le_one_div_of_le (mul_pos hδ hp) hg
          _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
      _ = (∑ j ∈ lo, 1 / ((i.val - j.val : ℕ) : ℝ)) / δ :=
        (Finset.sum_div ..).symm
      _ ≤ H N / δ := div_le_div_of_nonneg_right (lower_reciprocal_sum_le i) hδ.le
  have hhi : (∑ j ∈ hi, 1 / |f i - f j|) ≤ H N / δ := by
    calc
      _ ≤ ∑ j ∈ hi, (1 / ((j.val - i.val : ℕ) : ℝ)) / δ := by
        apply Finset.sum_le_sum
        intro j hj
        have hij : i < j := (Finset.mem_filter.mp hj).2
        have hg := ordered_gap f δ hf hsep hij.le
        have hc : ((j.val - i.val : ℕ) : ℝ) = (j : ℝ) - (i : ℝ) :=
          Nat.cast_sub hij.le
        rw [abs_sub_comm, abs_of_pos (sub_pos.mpr (hf hij)), hc]
        have hp : 0 < (j : ℝ) - (i : ℝ) :=
          sub_pos.mpr (by exact_mod_cast hij)
        calc
          1 / (f j - f i) ≤ 1 / (δ * ((j : ℝ) - (i : ℝ))) :=
            one_div_le_one_div_of_le (mul_pos hδ hp) hg
          _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
      _ = (∑ j ∈ hi, 1 / ((j.val - i.val : ℕ) : ℝ)) / δ :=
        (Finset.sum_div ..).symm
      _ ≤ H N / δ := div_le_div_of_nonneg_right (upper_reciprocal_sum_le i) hδ.le
  rw [hsplit, Finset.sum_union hdisj]
  calc
    _ ≤ H N / δ + H N / δ := add_le_add hlo hhi
    _ = _ := by ring

theorem row_le (s : Finset ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ |x - y|)
    (x : ℝ) (hx : x ∈ s) :
    (∑ y ∈ s.erase x, 1 / |x - y|) ≤ 2 * H s.card / δ := by
  let e := s.orderIsoOfFin rfl
  let f := s.orderEmbOfFin rfl
  let i : Fin s.card := e.symm ⟨x, hx⟩
  have hfi : f i = x := by
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
  have hbound := ordered_row_le f δ hδ f.strictMono
    (fun i j hij => hsep (f i) (s.orderEmbOfFin_mem rfl i)
      (f j) (s.orderEmbOfFin_mem rfl j) (f.injective.ne hij)) i
  have himage : (Finset.univ.erase i).image f = s.erase x := by
    rw [Finset.image_erase f.injective, s.image_orderEmbOfFin_univ, hfi]
  rw [← himage, Finset.sum_image f.injective.injOn]
  simpa only [hfi] using hbound

end Erdos374.PairSpacingHarmonic

