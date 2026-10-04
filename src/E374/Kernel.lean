import E374.Basic
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Choose.Factorization

/-!
# Squarefree kernels of a block of consecutive integers

For a square configuration `q_a * P_h(m) = □` (with `h ≤ m`),
  `∏_{i<h} sf(m - i) ≤ q_a * h^h * 4^h`,
because a prime `p > h` divides at most one block member (so its kernel exponent is
matched by `q_a`), while a prime `p ≤ h` divides at most `h/p + 1` block members.
Also: the two smallest of `h ≥ 2` positive numbers satisfy `(f i f j)^h ≤ (∏ f)^2`.
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

/-- Every positive integer is its kernel times a square. -/
theorem sf_mul_sq {n : ℕ} (hn : n ≠ 0) : ∃ u : ℕ, n = sf n * u ^ 2 := by
  have hsq : IsSquare (sf n * n) := (isSquare_sf_mul_iff hn n).mpr ⟨n, rfl⟩
  obtain ⟨k, hk⟩ := sf_dvd hn
  have hs0 : sf n ≠ 0 := sf_ne_zero n
  generalize sf n = s at hsq hk hs0 ⊢
  subst hk
  have hsq' : IsSquare (s * s * k) := by rwa [← mul_assoc] at hsq
  obtain ⟨u, hu⟩ := isSquare_of_mul_sq hs0 hsq'
  exact ⟨u, by rw [hu]; ring⟩

/-- Factorization of a product of distinct primes. -/
theorem factorization_prod_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (q : ℕ) :
    (∏ p ∈ S, p).factorization q = if q ∈ S then 1 else 0 := by
  rw [Nat.factorization_prod (fun x hx => (hS x hx).ne_zero), Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (fun x hx => by rw [(hS x hx).factorization, Finsupp.single_apply])]
  exact Finset.sum_ite_eq' _ _ _

/-- Legendre, first term: `n / p ≤ v_p(n!)`. -/
theorem div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (n : ℕ) :
    n / p ≤ (n.factorial).factorization p := by
  rw [Nat.factorization_factorial hp (b := Nat.log p n + 2) (by omega)]
  have hmem : 1 ∈ Finset.Ico 1 (Nat.log p n + 2) := by simp
  have := Finset.single_le_sum (f := fun i => n / p ^ i) (fun i _ => Nat.zero_le _) hmem
  simpa using this

/-- At most `h/p + 1` members of a block of length `h` are divisible by `p`. -/
theorem card_block_dvd_le {p h m : ℕ} (hp : 0 < p) (hhm : h ≤ m) :
    ((Finset.range h).filter (fun i => p ∣ m - i)).card ≤ h / p + 1 := by
  have hmaps : Set.MapsTo (fun i => i / p) ((Finset.range h).filter (fun i => p ∣ m - i) : Set ℕ)
      (Finset.range (h / p + 1) : Set ℕ) := by
    intro i hi
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi
    simp only [Finset.coe_range, Set.mem_Iio]
    have : i / p ≤ h / p := Nat.div_le_div_right hi.1.le
    omega
  have hinj : Set.InjOn (fun i => i / p)
      ((Finset.range h).filter (fun i => p ∣ m - i) : Set ℕ) := by
    intro i hi i' hi' hq
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi hi'
    simp only at hq
    have him : i ≤ m := by omega
    have him' : i' ≤ m := by omega
    have h1 : i ≡ m [MOD p] := (Nat.modEq_iff_dvd' him).mpr hi.2
    have h2 : i' ≡ m [MOD p] := (Nat.modEq_iff_dvd' him').mpr hi'.2
    have hmod : i % p = i' % p := (h1.trans h2.symm)
    have e1 := Nat.div_add_mod i p
    have e2 := Nat.div_add_mod i' p
    rw [hq, hmod] at e1
    omega
  have := Finset.card_le_card_of_injOn (fun i => i / p) hmaps hinj
  simpa using this

/-- `∑ f ≤ #{f ≠ 0}` when `f ≤ 1`. -/
theorem sum_le_card_filter_of_le_one {s : Finset ℕ} {f : ℕ → ℕ} {P : ℕ → Prop}
    [DecidablePred P] (h1 : ∀ i ∈ s, f i ≤ 1) (hP : ∀ i ∈ s, f i ≠ 0 → P i) :
    ∑ i ∈ s, f i ≤ (s.filter P).card := by
  rw [Finset.card_filter]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hp : P i
  · rw [if_pos hp]; exact h1 i hi
  · rw [if_neg hp]
    by_contra hc
    exact hp (hP i hi (by omega))

/-- **Kernel product bound.** -/
theorem kernel_prod_le {a h m : ℕ} (hhm : h ≤ m) (hs : IsSquare (q a * falling h m)) :
    ∏ i ∈ Finset.range h, sf (m - i) ≤ q a * (h ^ h * 4 ^ h) := by
  have hne : ∀ i ∈ Finset.range h, m - i ≠ 0 := by
    intro i hi; rw [Finset.mem_range] at hi; omega
  have hLne : ∏ i ∈ Finset.range h, sf (m - i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => sf_ne_zero _)
  have hW : h.factorial * primorial h ≠ 0 :=
    mul_ne_zero (Nat.factorial_ne_zero h) (primorial_ne_zero h)
  have hdvd : ∏ i ∈ Finset.range h, sf (m - i) ∣ q a * (h.factorial * primorial h) := by
    rw [← Nat.factorization_le_iff_dvd hLne (mul_ne_zero (q_ne_zero a) hW)]
    intro p
    by_cases hp : p.Prime
    swap
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp]; exact Nat.zero_le _
    rw [Nat.factorization_prod (fun i _ => sf_ne_zero _), Finsupp.finsetSum_apply]
    rw [Nat.factorization_mul (q_ne_zero a) hW, Nat.factorization_mul (Nat.factorial_ne_zero h)
      (primorial_ne_zero h)]
    simp only [Finsupp.coe_add, Pi.add_apply]
    -- each kernel exponent is ≤ 1 and nonzero only if `p ∣ m - i`
    have hsum_le : ∑ i ∈ Finset.range h, (sf (m - i)).factorization p ≤
        ((Finset.range h).filter (fun i => p ∣ m - i)).card := by
      apply sum_le_card_filter_of_le_one
      · intro i _; exact sf_factorization_le_one _ _
      · intro i hi hne0
        have hle := sf_factorization_le (m - i) p
        have : (m - i).factorization p ≠ 0 := by omega
        exact Nat.dvd_of_factorization_pos this
    have hcount := card_block_dvd_le (p := p) hp.pos hhm
    by_cases hph : p ≤ h
    · -- small primes: use `v_p(h!) ≥ h/p` and `v_p(primorial h) = 1`
      have hfact := div_le_factorization_factorial hp h
      have hprim : (primorial h).factorization p = 1 := by
        rw [primorial, factorization_prod_primes (fun x hx => (Finset.mem_filter.mp hx).2)]
        rw [if_pos (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩)]
      omega
    · -- large primes: at most one block member, matched by `q a` through parity
      push_neg at hph
      have hdiv0 : h / p = 0 := Nat.div_eq_of_lt hph
      have hle1 : ∑ i ∈ Finset.range h, (sf (m - i)).factorization p ≤ 1 := by omega
      have hq1 : (q a).factorization p ≤ 1 := sf_factorization_le_one _ _
      -- parity: ∑ kernel exponents ≡ v_p(falling) ≡ v_p(q a)  (mod 2)
      have hpar1 : (∑ i ∈ Finset.range h, (sf (m - i)).factorization p) % 2 =
          (falling h m).factorization p % 2 := by
        have hf : (falling h m).factorization p = ∑ i ∈ Finset.range h, (m - i).factorization p := by
          unfold falling
          rw [Nat.factorization_prod hne, Finsupp.finsetSum_apply]
        rw [hf]
        have e1 := Finset.sum_nat_mod (Finset.range h) 2 (fun i => (sf (m - i)).factorization p)
        have e2 := Finset.sum_nat_mod (Finset.range h) 2 (fun i => (m - i).factorization p)
        rw [e1, e2]
        congr 1
        exact Finset.sum_congr rfl (fun i _ => sf_factorization_mod_two _ _)
      have hpar2 : ((q a).factorization p + (falling h m).factorization p) % 2 = 0 := by
        have hsq := (Nat.isSquare_iff_even_factorization.mp hs) p hp
        rw [Nat.factorization_mul (q_ne_zero a) (falling_ne_zero hhm)] at hsq
        simp only [Finsupp.coe_add, Pi.add_apply] at hsq
        exact Nat.even_iff.mp hsq
      omega
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero (mul_ne_zero (q_ne_zero a) hW)) hdvd
  calc ∏ i ∈ Finset.range h, sf (m - i) ≤ q a * (h.factorial * primorial h) := hle
    _ ≤ q a * (h ^ h * 4 ^ h) := by
        apply Nat.mul_le_mul_left
        exact Nat.mul_le_mul (Nat.factorial_le_pow h) (primorial_le_four_pow h)

/-- **Two smallest values.** For `h ≥ 2` positive values on `range h`, there are positions
`i < j < h` with `(f i * f j)^h ≤ (∏ f)^2`. -/
theorem exists_two_small (f : ℕ → ℕ) {h : ℕ} (hh : 2 ≤ h) :
    ∃ i j : ℕ, i < j ∧ j < h ∧
      (f i * f j) ^ h ≤ (∏ k ∈ Finset.range h, f k) ^ 2 := by
  classical
  have hne : (Finset.range h).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨i0, hi0, hmin0⟩ := Finset.exists_min_image (Finset.range h) f hne
  have hne' : ((Finset.range h).erase i0).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hi0, Finset.card_range]; omega
  obtain ⟨j0, hj0, hmin1⟩ := Finset.exists_min_image ((Finset.range h).erase i0) f hne'
  have hij : i0 ≠ j0 := (Finset.ne_of_mem_erase hj0).symm
  have hj0r : j0 ∈ Finset.range h := Finset.mem_of_mem_erase hj0
  have hfij : f i0 ≤ f j0 := hmin0 j0 hj0r
  have hprod : ∏ k ∈ Finset.range h, f k = f i0 * ∏ k ∈ (Finset.range h).erase i0, f k :=
    (Finset.mul_prod_erase _ _ hi0).symm
  have hcard : ((Finset.range h).erase i0).card = h - 1 := by
    rw [Finset.card_erase_of_mem hi0, Finset.card_range]
  have hlow : f j0 ^ (h - 1) ≤ ∏ k ∈ (Finset.range h).erase i0, f k := by
    have := Finset.pow_card_le_prod ((Finset.range h).erase i0) f (f j0) hmin1
    rwa [hcard] at this
  have key : (f i0 * f j0) ^ h ≤ (∏ k ∈ Finset.range h, f k) ^ 2 := by
    obtain ⟨k, rfl⟩ : ∃ k, h = k + 2 := ⟨h - 2, by omega⟩
    have h1 : (f i0 * f j0) ^ (k + 2) = f i0 ^ 2 * f j0 ^ 2 * (f i0 ^ k * f j0 ^ k) := by ring
    have h2 : f i0 ^ k ≤ f j0 ^ k := Nat.pow_le_pow_left hfij k
    have h3 : (∏ k' ∈ Finset.range (k + 2), f k') ^ 2 ≥ (f i0 * f j0 ^ (k + 1)) ^ 2 := by
      rw [hprod]
      apply Nat.pow_le_pow_left
      apply Nat.mul_le_mul_left
      simpa using hlow
    have h4 : (f i0 * f j0 ^ (k + 1)) ^ 2 = f i0 ^ 2 * f j0 ^ 2 * (f j0 ^ k * f j0 ^ k) := by ring
    rw [h1]
    calc f i0 ^ 2 * f j0 ^ 2 * (f i0 ^ k * f j0 ^ k)
        ≤ f i0 ^ 2 * f j0 ^ 2 * (f j0 ^ k * f j0 ^ k) := by
          apply Nat.mul_le_mul_left
          exact Nat.mul_le_mul_right _ h2
      _ = (f i0 * f j0 ^ (k + 1)) ^ 2 := h4.symm
      _ ≤ _ := h3
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact ⟨i0, j0, hlt, Finset.mem_range.mp hj0r, key⟩
  · refine ⟨j0, i0, hgt, Finset.mem_range.mp hi0, ?_⟩
    rw [mul_comm]; exact key

end Erdos374.D35

end
