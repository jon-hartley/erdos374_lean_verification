import E374.D3

/-!
# The D3 asymptotic `D3(X) = κ₃ √X + O(X^{2/5+ε})`

`κ₃ = ∑_{q ∈ Q, q ≠ 1} q^{-1/2}`, the sum running over the DISTINCT squarefree kernels
`q = q_a` (`a ≥ 1`), each counted once. Endpoints with consecutive top indices are exactly
`q u²` with `q ∈ Q \ {1}`, up to finitely many ordering exceptions; distinct `q` give
disjoint families. Inputs as for `D3_order`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
set_option maxHeartbeats 3200000

noncomputable section
open scoped BigOperators
open Finset

namespace Erdos374.D35

/-- Distinct nontrivial factorial kernels. -/
def Qset : Set ℕ := {q | q ≠ 1 ∧ ∃ a : ℕ, 1 ≤ a ∧ q = Erdos374.q a}

open Classical in
/-- Summand of `κ₃`. -/
def kappaTerm (q : ℕ) : ℝ := if q ∈ Qset then (q : ℝ) ^ (-(1 / 2 : ℝ)) else 0

/-- `κ₃`. -/
def kappa3 : ℝ := ∑' q : ℕ, kappaTerm q

theorem kappaTerm_nonneg (q : ℕ) : 0 ≤ kappaTerm q := by
  unfold kappaTerm; split_ifs <;> positivity

open Classical in
/-- Least index of a kernel. -/
noncomputable def leastIndex (q : ℕ) : ℕ :=
  if h : ∃ a : ℕ, 1 ≤ a ∧ q = Erdos374.q a then Nat.find h else 0

open Classical in
theorem leastIndex_spec {q : ℕ} (hq : q ∈ Qset) :
    1 ≤ leastIndex q ∧ q = Erdos374.q (leastIndex q) := by
  have h : ∃ a : ℕ, 1 ≤ a ∧ q = Erdos374.q a := hq.2
  unfold leastIndex
  rw [dif_pos h]
  exact Nat.find_spec h

open Classical in
theorem leastIndex_le {q a : ℕ} (hq : q ∈ Qset) (ha : 1 ≤ a) (hqa : q = Erdos374.q a) :
    leastIndex q ≤ a := by
  have h : ∃ a : ℕ, 1 ≤ a ∧ q = Erdos374.q a := hq.2
  unfold leastIndex
  rw [dif_pos h]
  exact Nat.find_min' h ⟨ha, hqa⟩

/-- Weighted kernel sums are uniformly bounded (geometric decay from growth). -/
theorem kernel_weight_sum_le (hG : Tasks.FactorialClassGrowth) (β : ℝ) (hβ : 0 < β) :
    ∃ K : ℝ, ∀ S : Finset ℕ, (∀ q ∈ S, q ∈ Qset) →
      ∑ q ∈ S, (q : ℝ) ^ (-β) ≤ K := by
  classical
  obtain ⟨N₀, hN₀⟩ := hG
  set r : ℝ := Real.exp (-(β / 3)) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by rw [hr, Real.exp_lt_one_iff]; linarith
  refine ⟨N₀ + (1 - r)⁻¹, fun S hS => ?_⟩
  set g : ℕ → ℝ := fun a => if a < N₀ then 1 else r ^ a with hg
  have hterm : ∀ q ∈ S, (q : ℝ) ^ (-β) ≤ g (leastIndex q) := by
    intro q hq
    obtain ⟨h1, hqa⟩ := leastIndex_spec (hS q hq)
    have hq1 : (1 : ℝ) ≤ q := by rw [hqa]; exact_mod_cast q_pos _
    simp only [hg]
    by_cases ha : leastIndex q < N₀
    · rw [if_pos ha]
      exact Real.rpow_le_one_of_one_le_of_nonpos hq1 (by linarith)
    · rw [if_neg ha]
      push_neg at ha
      have hexp := hN₀ (leastIndex q) ha
      rw [← hqa] at hexp
      have h2 : (q : ℝ) ^ (-β) ≤ (Real.exp ((leastIndex q : ℝ) / 3)) ^ (-β) :=
        Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hexp (by linarith)
      have h3 : (Real.exp ((leastIndex q : ℝ) / 3)) ^ (-β) = r ^ (leastIndex q) := by
        rw [← Real.exp_mul, hr, ← Real.exp_nat_mul]; congr 1; ring
      linarith
  have hinj : Set.InjOn leastIndex (S : Set ℕ) := by
    intro q hq q' hq' h
    have := (leastIndex_spec (hS q hq)).2
    have := (leastIndex_spec (hS q' hq')).2
    try simp only at h
    rw [‹q = _›, ‹q' = _›, h]
  have hgnn : ∀ a, 0 ≤ g a := fun a => by simp only [hg]; split_ifs <;> positivity
  set M := (S.image leastIndex).sup id + 1
  calc ∑ q ∈ S, (q : ℝ) ^ (-β) ≤ ∑ q ∈ S, g (leastIndex q) := Finset.sum_le_sum hterm
    _ = ∑ a ∈ S.image leastIndex, g a := (Finset.sum_image hinj).symm
    _ ≤ ∑ a ∈ Finset.range M, g a := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro a ha
          rw [Finset.mem_range]
          have := Finset.le_sup (f := id) ha
          simp only [id] at this
          omega
        · intro a _ _; exact hgnn a
    _ ≤ ∑ a ∈ Finset.range M, ((if a < N₀ then (1 : ℝ) else 0) + r ^ a) := by
        apply Finset.sum_le_sum; intro a _
        simp only [hg]; split_ifs <;> simp [hr0.le, pow_nonneg]
        all_goals positivity
    _ = ∑ a ∈ Finset.range M, (if a < N₀ then (1 : ℝ) else 0) + ∑ a ∈ Finset.range M, r ^ a :=
        Finset.sum_add_distrib
    _ ≤ N₀ + (1 - r)⁻¹ := by
        apply add_le_add
        · rw [Finset.sum_boole]
          have : ((Finset.range M).filter (fun a => a < N₀)).card ≤ N₀ := by
            calc _ ≤ (Finset.range N₀).card := Finset.card_le_card (by
                  intro a ha; rw [Finset.mem_filter] at ha; exact Finset.mem_range.mpr ha.2)
              _ = N₀ := Finset.card_range _
          exact_mod_cast this
        · exact geom_sum_le_inv hr0.le hr1 _

theorem kappaTerm_summable (hG : Tasks.FactorialClassGrowth) : Summable kappaTerm := by
  classical
  obtain ⟨K, hK⟩ := kernel_weight_sum_le hG (1 / 2) (by norm_num)
  refine summable_of_sum_range_le (c := K) kappaTerm_nonneg (fun n => ?_)
  have : ∑ i ∈ Finset.range n, kappaTerm i =
      ∑ q ∈ (Finset.range n).filter (· ∈ Qset), (q : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Finset.sum_filter]; rfl
  rw [this]
  exact hK _ (fun q hq => (Finset.mem_filter.mp hq).2)

/-- Tail of `κ₃`: `∑_{q > X} q^{-1/2} ≤ K' X^{-1/4}`. -/
theorem kappa3_tail (hG : Tasks.FactorialClassGrowth) :
    ∃ K : ℝ, ∀ X : ℕ, 1 ≤ X →
      |kappa3 - ∑ q ∈ Finset.range (X + 1), kappaTerm q| ≤ K * (X : ℝ) ^ (-(1 / 4 : ℝ)) := by
  classical
  obtain ⟨K, hK⟩ := kernel_weight_sum_le hG (1 / 4) (by norm_num)
  have hsum := kappaTerm_summable hG
  refine ⟨max K 0, fun X hX => ?_⟩
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hsplit := hsum.sum_add_tsum_nat_add (X + 1)
  have htail : ∑' i, kappaTerm (i + (X + 1)) ≤ max K 0 * (X : ℝ) ^ (-(1 / 4 : ℝ)) := by
    apply Real.tsum_le_of_sum_range_le (fun i => kappaTerm_nonneg _)
    intro n
    have h1 : ∀ i ∈ Finset.range n, kappaTerm (i + (X + 1)) ≤
        (X : ℝ) ^ (-(1 / 4 : ℝ)) *
          (if i + (X + 1) ∈ Qset then ((i + (X + 1) : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) else 0) := by
      intro i _
      unfold kappaTerm
      split_ifs
      · have hq : (X : ℝ) < ((i + (X + 1) : ℕ) : ℝ) := by push_cast; linarith
        have hq0 : (0 : ℝ) < ((i + (X + 1) : ℕ) : ℝ) := by linarith
        have e : ((i + (X + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) =
            ((i + (X + 1) : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) * ((i + (X + 1) : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) := by
          rw [← Real.rpow_add hq0]; norm_num
        rw [e, mul_comm ((X : ℝ) ^ _)]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow_of_nonpos hX0 hq.le (by norm_num)
      · simp
    calc ∑ i ∈ Finset.range n, kappaTerm (i + (X + 1))
        ≤ ∑ i ∈ Finset.range n, (X : ℝ) ^ (-(1 / 4 : ℝ)) *
            (if i + (X + 1) ∈ Qset then ((i + (X + 1) : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) else 0) :=
          Finset.sum_le_sum h1
      _ = (X : ℝ) ^ (-(1 / 4 : ℝ)) * ∑ i ∈ Finset.range n,
            (if i + (X + 1) ∈ Qset then ((i + (X + 1) : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) else 0) := by
          rw [Finset.mul_sum]
      _ ≤ (X : ℝ) ^ (-(1 / 4 : ℝ)) * max K 0 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [← Finset.sum_filter]
          have hinj : Set.InjOn (fun i => i + (X + 1))
              (((Finset.range n).filter (fun i => i + (X + 1) ∈ Qset)) : Set ℕ) := by
            intro a _ b _ h; simp only at h; omega
          rw [← Finset.sum_image (g := fun i => i + (X + 1))
            (f := fun q : ℕ => (q : ℝ) ^ (-(1 / 4 : ℝ))) hinj]
          refine le_trans (hK _ ?_) (le_max_left _ _)
          intro q hq
          rw [Finset.mem_image] at hq
          obtain ⟨i, hi, rfl⟩ := hq
          exact (Finset.mem_filter.mp hi).2
      _ = max K 0 * (X : ℝ) ^ (-(1 / 4 : ℝ)) := by ring
  have hnn : 0 ≤ ∑' i, kappaTerm (i + (X + 1)) := tsum_nonneg (fun i => kappaTerm_nonneg _)
  unfold kappa3
  rw [← hsplit]
  rw [show ∑ i ∈ Finset.range (X + 1), kappaTerm i + ∑' i, kappaTerm (i + (X + 1)) -
      ∑ q ∈ Finset.range (X + 1), kappaTerm q = ∑' i, kappaTerm (i + (X + 1)) by ring]
  rw [abs_of_nonneg hnn]
  exact htail

/-! ## The consecutive family -/

/-- Exact consecutive endpoints with a nontrivial kernel. -/
def ConsQ : Set ℕ := {m | ∃ a : ℕ, 1 ≤ a ∧ a + 1 < m ∧ q a ≠ 1 ∧ IsSquare (q a * m)}

theorem D3_subset_ConsQ_union : D3 ⊆ ConsQ ∪ ESet := by
  rintro m ⟨hm1, h3, h2⟩
  obtain ⟨a, h, ha, hh, hahm, hs⟩ := hasRep_three_iff_reduced.mp h3
  rcases Nat.lt_or_ge h 2 with hlt | hge
  · have : h = 1 := by omega
    subst this
    left
    refine ⟨a, ha, by omega, ?_, by simpa [falling] using hs⟩
    intro hq
    rw [hq, one_mul, falling_one'] at hs
    exact h2 (hasRep_two_of_square (by omega) hs)
  · right; exact ⟨a, h, hge, hahm, hs⟩

theorem ConsQ_subset_D3_union : ConsQ ⊆ D3 ∪ ESet := by
  rintro m ⟨a, ha, ham, hq1, hs⟩
  by_cases hE : m ∈ ESet
  · exact Or.inr hE
  left
  refine ⟨by omega, ?_, ?_⟩
  · rw [hasRep_three_iff_reduced]
    exact ⟨a, 1, ha, le_refl 1, ham, by simpa [falling] using hs⟩
  · intro h2
    rcases two_rep_cases h2 with hsq | hE'
    · -- `m` square and `q_a m` square ⇒ `q_a` square ⇒ `q_a = 1`
      obtain ⟨t, ht⟩ := hsq
      have hm0 : t ≠ 0 := by rintro rfl; simp at ht; omega
      have hqs : IsSquare (t * t * q a) := by
        have e : q a * m = t * t * q a := by rw [ht]; ring
        rwa [e] at hs
      have := isSquare_of_mul_sq hm0 hqs
      obtain ⟨w, hw⟩ := this
      have hsqf := squarefree_q a
      rw [hw] at hsqf
      have hw1 : IsUnit w := hsqf w (dvd_refl _)
      rw [Nat.isUnit_iff] at hw1
      rw [hw, hw1] at hq1
      exact hq1 rfl
    · exact hE hE'

/-- The full family `W = {q u² : q ∈ Qset, u ≥ 1}`. -/
def Wfam : Set ℕ := {m | ∃ q u : ℕ, q ∈ Qset ∧ 1 ≤ u ∧ m = q * u ^ 2}

theorem ConsQ_subset_Wfam : ConsQ ⊆ Wfam := by
  rintro m ⟨a, ha, ham, hq1, hs⟩
  obtain ⟨u, hu⟩ := eq_q_mul_sq_of_isSquare hs
  have hu1 : 1 ≤ u := by
    rcases Nat.eq_zero_or_pos u with h0 | h0
    · rw [h0] at hu; simp at hu; omega
    · exact h0
  exact ⟨q a, u, ⟨hq1, a, ha, rfl⟩, hu1, hu⟩

/-- Ordering exceptions are finitely many. -/
theorem Wfam_diff_ConsQ_finite (hG : Tasks.FactorialClassGrowth) :
    ∃ B : ℕ, Wfam \ ConsQ ⊆ Initial B := by
  obtain ⟨N₀, hN₀⟩ := hG
  -- `a + 2 < e^{a/3}` for `a ≥ 18`
  obtain ⟨A, hA⟩ : ∃ A : ℕ, ∀ a : ℕ, A ≤ a → (a : ℝ) + 2 < Real.exp ((a : ℝ) / 3) := by
    refine ⟨18, fun a ha => ?_⟩
    have ha' : (18 : ℝ) ≤ a := by exact_mod_cast ha
    have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ (a : ℝ) / 3 by positivity)
    nlinarith
  refine ⟨max N₀ A + 2, ?_⟩
  rintro m ⟨⟨q', u, hq, hu, rfl⟩, hnot⟩
  obtain ⟨hl1, hlq⟩ := leastIndex_spec hq
  simp only [Initial, Set.mem_setOf_eq]
  by_contra hbig
  push_neg at hbig
  apply hnot
  by_cases hord : leastIndex q' + 1 < q' * u ^ 2
  · refine ⟨leastIndex q', hl1, hord, ?_, ?_⟩
    · rw [← hlq]; exact hq.1
    · rw [← hlq]; exact ⟨q' * u, by ring⟩
  · exfalso
    push_neg at hord
    -- `q' ≤ leastIndex q' + 1` while `q' = q_{a} ≥ e^{a/3}` for large `a`
    have hq'le : q' ≤ leastIndex q' + 1 := le_trans (Nat.le_mul_of_pos_right _
      (Nat.one_le_pow _ _ hu)) hord
    have hbig' : max N₀ A + 2 ≤ q' * u ^ 2 := hbig
    by_cases hsmall : leastIndex q' < max N₀ A
    · omega
    · push_neg at hsmall
      have h1 := hN₀ (leastIndex q') (le_trans (le_max_left _ _) hsmall)
      have h2 := hA (leastIndex q') (le_trans (le_max_right _ _) hsmall)
      rw [← hlq] at h1
      have : (q' : ℝ) ≤ (leastIndex q' : ℝ) + 1 := by exact_mod_cast hq'le
      linarith

open Classical in
/-- Counting `W` by kernels: `#W(X) = ∑_{q ∈ Qset, q ≤ X} ⌊√(X/q)⌋`. -/
theorem prefixCount_Wfam_eq (X : ℕ) :
    prefixCount Wfam X =
      ∑ q ∈ (Finset.range (X + 1)).filter (· ∈ Qset), Nat.sqrt (X / q) := by
  classical
  set S := (Finset.range (X + 1)).filter (· ∈ Qset)
  have hfam : (Finset.Icc 1 X).filter (fun m => m ∈ Wfam) =
      S.biUnion (fun q => (Finset.Icc 1 (Nat.sqrt (X / q))).image (fun u => q * u ^ 2)) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_biUnion, Finset.mem_image, S,
      Finset.mem_range]
    constructor
    · rintro ⟨⟨hm1, hmX⟩, q, u, hq, hu, rfl⟩
      have hq1 : 1 ≤ q := by obtain ⟨_, a, _, rfl⟩ := hq; exact q_pos a
      have hqX : q ≤ X := le_trans (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hu)) hmX
      refine ⟨q, ⟨by omega, hq⟩, u, ⟨hu, ?_⟩, rfl⟩
      rw [Nat.le_sqrt', Nat.le_div_iff_mul_le hq1, mul_comm]; exact hmX
    · rintro ⟨q, ⟨_, hq⟩, u, ⟨hu, hus⟩, rfl⟩
      have hq1 : 1 ≤ q := by obtain ⟨_, a, _, rfl⟩ := hq; exact q_pos a
      rw [Nat.le_sqrt', Nat.le_div_iff_mul_le hq1, mul_comm] at hus
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by positivity)), hus⟩,
        q, u, hq, hu, rfl⟩
  have hdisj : (S : Set ℕ).PairwiseDisjoint
      (fun q => (Finset.Icc 1 (Nat.sqrt (X / q))).image (fun u => q * u ^ 2)) := by
    intro q hq q' hq' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro m hm hm'
    rw [Finset.mem_image] at hm hm'
    obtain ⟨u, hu, rfl⟩ := hm
    obtain ⟨u', hu', heq⟩ := hm'
    apply hne
    have hqS := (Finset.mem_filter.mp hq).2
    have hq'S := (Finset.mem_filter.mp hq').2
    obtain ⟨_, a, _, rfl⟩ := hqS
    obtain ⟨_, a', _, rfl⟩ := hq'S
    -- `q_a u² = q_{a'} u'²` with both kernels squarefree ⇒ equal
    have hu0 : u ≠ 0 := by rw [Finset.mem_Icc] at hu; omega
    have hsq : IsSquare (q a * q a') := by
      have hs : IsSquare ((q a * u ^ 2) * (q a' * u' ^ 2)) := by
        rw [← heq]; exact ⟨q a' * u' ^ 2, rfl⟩
      have : (q a * u ^ 2) * (q a' * u' ^ 2) = (u * u') * (u * u') * (q a * q a') := by ring
      rw [this] at hs
      have hu'0 : u' ≠ 0 := by rw [Finset.mem_Icc] at hu'; omega
      exact isSquare_of_mul_sq (mul_ne_zero hu0 hu'0) hs
    have := (squarefree_q a).dvd_of_isSquare_mul hsq
    have hsq' : IsSquare (q a' * q a) := by rwa [mul_comm] at hsq
    have := (squarefree_q a').dvd_of_isSquare_mul hsq'
    exact Nat.dvd_antisymm ‹q a ∣ q a'› ‹q a' ∣ q a›
  unfold prefixCount
  rw [hfam, Finset.card_biUnion hdisj]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  have hq1 : 1 ≤ q := by obtain ⟨_, a, _, rfl⟩ := (Finset.mem_filter.mp hq).2; exact q_pos a
  rw [Finset.card_image_of_injOn, Nat.card_Icc, Nat.add_sub_cancel]
  intro u _ v _ h
  simp only at h
  have : u ^ 2 = v ^ 2 := Nat.eq_of_mul_eq_mul_left (by omega) h
  exact Nat.pow_left_injective (by norm_num) this

open Classical in
/-- Number of distinct kernels up to `X`: `≤ N₁ + 3 log X + 1`. -/
theorem card_Qset_le (hG : Tasks.FactorialClassGrowth) :
    ∃ N₁ : ℕ, ∀ X : ℕ, 1 ≤ X →
      (((Finset.range (X + 1)).filter (· ∈ Qset)).card : ℝ) ≤ N₁ + 3 * Real.log X + 1 := by
  classical
  obtain ⟨N₁, hN₁⟩ := hG
  refine ⟨N₁, fun X hX => ?_⟩
  have hX1R : (1 : ℝ) ≤ X := by exact_mod_cast hX
  set S := (Finset.range (X + 1)).filter (· ∈ Qset)
  have hinj : Set.InjOn leastIndex (S : Set ℕ) := by
    intro q hq q' hq' h
    have e1 := (leastIndex_spec (Finset.mem_filter.mp hq).2).2
    have e2 := (leastIndex_spec (Finset.mem_filter.mp hq').2).2
    try simp only at h
    rw [e1, e2, h]
  have hsub : S.image leastIndex ⊆ Finset.range N₁ ∪ Finset.range (⌊3 * Real.log X⌋₊ + 1) := by
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨q', hq', rfl⟩ := ha
    have hqS := Finset.mem_filter.mp hq'
    obtain ⟨_, hqa⟩ := leastIndex_spec hqS.2
    have hqX : q' ≤ X := by have := Finset.mem_range.mp hqS.1; omega
    rw [Finset.mem_union, Finset.mem_range, Finset.mem_range]
    by_cases ha : N₁ ≤ leastIndex q'
    · right
      have h1 := hN₁ _ ha
      rw [← hqa] at h1
      have h2 : Real.exp ((leastIndex q' : ℝ) / 3) ≤ X := le_trans h1 (by exact_mod_cast hqX)
      have h3 : (leastIndex q' : ℝ) / 3 ≤ Real.log X := by
        have := Real.log_le_log (Real.exp_pos _) h2; rwa [Real.log_exp] at this
      have : leastIndex q' ≤ ⌊3 * Real.log X⌋₊ := Nat.le_floor (by linarith)
      omega
    · left; omega
  have hc := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  rw [Finset.card_image_of_injOn hinj, Finset.card_range, Finset.card_range] at hc
  have hfl : (⌊3 * Real.log X⌋₊ : ℝ) ≤ 3 * Real.log X :=
    Nat.floor_le (by have := Real.log_nonneg hX1R; positivity)
  have : (S.card : ℝ) ≤ ((N₁ + (⌊3 * Real.log X⌋₊ + 1) : ℕ) : ℝ) := by exact_mod_cast hc
  push_cast at this
  linarith

/-- `|⌊√(X/q)⌋ - √X q^{-1/2}| ≤ 1`. -/
theorem nat_sqrt_div_close {X q : ℕ} (hq : 1 ≤ q) :
    |((Nat.sqrt (X / q) : ℕ) : ℝ) - Real.sqrt X * (q : ℝ) ^ (-(1 / 2 : ℝ))| ≤ 1 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have e : Real.sqrt X * (q : ℝ) ^ (-(1 / 2 : ℝ)) = Real.sqrt ((X : ℝ) / q) := by
    rw [Real.sqrt_div' _ hq0.le, Real.rpow_neg hq0.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
  rw [e]
  set n := X / q
  have h1 : ((Nat.sqrt n : ℕ) : ℝ) ≤ Real.sqrt ((X : ℝ) / q) :=
    le_trans Real.nat_sqrt_le_real_sqrt (Real.sqrt_le_sqrt Nat.cast_div_le)
  have h2 : Real.sqrt ((X : ℝ) / q) ≤ ((Nat.sqrt n : ℕ) : ℝ) + 1 := by
    have hlt : (X : ℝ) / q < (n : ℝ) + 1 := by
      have := Nat.div_add_mod X q
      have hm := Nat.mod_lt X (show 0 < q by omega)
      have : (X : ℝ) = q * (n : ℝ) + ((X % q : ℕ) : ℝ) := by exact_mod_cast this.symm
      have : ((X % q : ℕ) : ℝ) < q := by exact_mod_cast hm
      rw [div_lt_iff₀ hq0]; nlinarith
    rw [Real.sqrt_le_left (by positivity)]
    have := Nat.lt_succ_sqrt n
    have : (n : ℝ) + 1 ≤ ((Nat.sqrt n + 1) * (Nat.sqrt n + 1) : ℕ) := by exact_mod_cast this
    push_cast at this; nlinarith
  rw [abs_le]; constructor <;> linarith

open Classical in
/-- **The D3 asymptotic** `D3(X) = κ₃ √X + O(X^{2/5+ε})`. -/
theorem D3_asymptotic (hRM : Tasks.ValuationOneMass) (hG : Tasks.FactorialClassGrowth)
    (hW : CoarseWeilBound) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      |(prefixCount D3 X : ℝ) - kappa3 * Real.sqrt X| ≤ C * (X : ℝ) ^ ((2 : ℝ) / 5 + ε) := by
  classical
  intro ε hε
  obtain ⟨CE, NE, hNE⟩ := ESet_count_le hRM hG hW ε hε
  obtain ⟨B, hB⟩ := Wfam_diff_ConsQ_finite hG
  obtain ⟨N₁, hN₁⟩ := card_Qset_le hG
  obtain ⟨Kt, hKt⟩ := kappa3_tail hG
  refine ⟨max CE 0 + B + N₁ + 10 + max Kt 0, max NE 1, fun X hX => ?_⟩
  have hXE : NE ≤ X := le_trans (le_max_left _ _) hX
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hX1R : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hX0R : (0 : ℝ) < X := by linarith
  set Y := (X : ℝ) ^ ((2 : ℝ) / 5 + ε) with hY
  have hY1 : (1 : ℝ) ≤ Y := Real.one_le_rpow hX1R (by linarith)
  -- E
  have hEle : (prefixCount ESet X : ℝ) ≤ max CE 0 * Y :=
    le_trans (hNE X hXE) (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  -- D3 vs ConsQ
  have h1 : (prefixCount D3 X : ℝ) ≤ prefixCount ConsQ X + prefixCount ESet X := by
    exact_mod_cast le_trans (prefixCount_mono D3_subset_ConsQ_union X)
      (prefixCount_union_le _ _ X)
  have h2 : (prefixCount ConsQ X : ℝ) ≤ prefixCount D3 X + prefixCount ESet X := by
    exact_mod_cast le_trans (prefixCount_mono ConsQ_subset_D3_union X)
      (prefixCount_union_le _ _ X)
  -- ConsQ vs Wfam
  have h3 : (prefixCount ConsQ X : ℝ) ≤ prefixCount Wfam X := by
    exact_mod_cast prefixCount_mono ConsQ_subset_Wfam X
  have h4 : (prefixCount Wfam X : ℝ) ≤ prefixCount ConsQ X + B := by
    have hpart := prefixCount_partition ConsQ Wfam X
    have hm : prefixCount (Wfam \ ConsQ) X ≤ B := by
      calc prefixCount (Wfam \ ConsQ) X ≤ prefixCount (Initial B) X := prefixCount_mono hB X
        _ ≤ B := by
          unfold prefixCount
          calc _ ≤ (Finset.range B).card := Finset.card_le_card (by
                intro m hm; rw [Finset.mem_filter] at hm; exact Finset.mem_range.mpr hm.2)
            _ = B := Finset.card_range B
    have hm2 : prefixCount (ConsQ ∩ Wfam) X ≤ prefixCount ConsQ X :=
      prefixCount_mono Set.inter_subset_left X
    have : prefixCount Wfam X ≤ prefixCount ConsQ X + B := by omega
    exact_mod_cast this
  -- Wfam vs √X ∑ q^{-1/2}
  set S := (Finset.range (X + 1)).filter (· ∈ Qset) with hS
  have hWeq : (prefixCount Wfam X : ℝ) = ∑ q ∈ S, ((Nat.sqrt (X / q) : ℕ) : ℝ) := by
    rw [prefixCount_Wfam_eq]; push_cast; rfl
  have hsumterm : ∑ q ∈ Finset.range (X + 1), kappaTerm q =
      ∑ q ∈ S, (q : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [hS, Finset.sum_filter]; rfl
  have h5 : |(prefixCount Wfam X : ℝ) - Real.sqrt X * ∑ q ∈ Finset.range (X + 1), kappaTerm q|
      ≤ S.card := by
    rw [hWeq, hsumterm, Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc |∑ q ∈ S, (((Nat.sqrt (X / q) : ℕ) : ℝ) - Real.sqrt X * (q : ℝ) ^ (-(1 / 2 : ℝ)))|
        ≤ ∑ q ∈ S, |((Nat.sqrt (X / q) : ℕ) : ℝ) - Real.sqrt X * (q : ℝ) ^ (-(1 / 2 : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _q ∈ S, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro q hq
          have hq1 : 1 ≤ q := by
            obtain ⟨_, a, _, rfl⟩ := (Finset.mem_filter.mp hq).2; exact q_pos a
          exact nat_sqrt_div_close hq1
      _ = S.card := by simp
  have hScard := hN₁ X hX1
  -- tail
  have h6 : |Real.sqrt X * ∑ q ∈ Finset.range (X + 1), kappaTerm q - kappa3 * Real.sqrt X| ≤
      max Kt 0 * (X : ℝ) ^ ((1 : ℝ) / 4) := by
    have ht := hKt X hX1
    have hs : Real.sqrt X * (X : ℝ) ^ (-(1 / 4 : ℝ)) = (X : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hX0R]; norm_num
    calc |Real.sqrt X * ∑ q ∈ Finset.range (X + 1), kappaTerm q - kappa3 * Real.sqrt X|
        = Real.sqrt X * |kappa3 - ∑ q ∈ Finset.range (X + 1), kappaTerm q| := by
          rw [← abs_of_nonneg (Real.sqrt_nonneg (X : ℝ)), ← abs_mul,
            abs_of_nonneg (Real.sqrt_nonneg (X : ℝ))]
          rw [← abs_neg]; congr 1; ring
      _ ≤ Real.sqrt X * (Kt * (X : ℝ) ^ (-(1 / 4 : ℝ))) :=
          mul_le_mul_of_nonneg_left ht (Real.sqrt_nonneg _)
      _ = Kt * (X : ℝ) ^ ((1 : ℝ) / 4) := by rw [← hs]; ring
      _ ≤ max Kt 0 * (X : ℝ) ^ ((1 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  -- size comparisons
  have hq4 : (X : ℝ) ^ ((1 : ℝ) / 4) ≤ Y := Real.rpow_le_rpow_of_exponent_le hX1R (by linarith)
  have hlog : Real.log X ≤ 3 * Y := by
    have h1 : Real.log X ≤ (X : ℝ) ^ ((2 : ℝ) / 5) / (2 / 5) := Real.log_le_rpow_div hX0R.le (by norm_num)
    have h2 : (X : ℝ) ^ ((2 : ℝ) / 5) ≤ Y := Real.rpow_le_rpow_of_exponent_le hX1R (by linarith)
    linarith
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ N₁ := Nat.cast_nonneg _
  have hK0 : 0 ≤ max Kt 0 := le_max_right _ _
  have hC0 : 0 ≤ max CE 0 := le_max_right _ _
  rw [abs_le] at h5 h6 ⊢
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hq4 hK0, mul_le_mul_of_nonneg_left hY1 hB0,
    mul_le_mul_of_nonneg_left hY1 hN0]

end Erdos374.D35

end
