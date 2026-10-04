import E374.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.ZMod.Basic

/-!
# Gallagher's larger sieve (fully proved)

If a finite set `T ⊆ [1, X]` lies, modulo each prime `p ∈ P`, in a set `Ω p` of at most
`ρ p` residue classes, then (for `T` nonempty)

  `|T| * (∑_{p∈P} log p / ρ p - log X) ≤ ∑_{p∈P} log p - log X`.

This is inequality (2.6) of the D3/D5 draft. The proof is the draft's Cauchy–Schwarz
argument on residue-class pair counts.
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

/-- The primes of `P` dividing a positive `d` contribute at most `log d`. -/
theorem sum_log_primes_dvd_le {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {d : ℕ} (hd : 0 < d) :
    ∑ p ∈ P.filter (fun p => p ∣ d), Real.log p ≤ Real.log d := by
  have hdvd : ∏ p ∈ P.filter (fun p => p ∣ d), p ∣ d :=
    Finset.prod_primes_dvd d (fun a ha => (hP a (Finset.mem_filter.1 ha).1).prime)
      (fun a ha => (Finset.mem_filter.1 ha).2)
  have hle : ∏ p ∈ P.filter (fun p => p ∣ d), p ≤ d := Nat.le_of_dvd hd hdvd
  have hpos : 0 < ∏ p ∈ P.filter (fun p => p ∣ d), p :=
    Finset.prod_pos (fun p hp => (hP p (Finset.mem_filter.1 hp).1).pos)
  rw [← Real.log_prod (fun p hp => by
    exact_mod_cast (hP p (Finset.mem_filter.1 hp).1).ne_zero)]
  rw [← Nat.cast_prod]
  exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)

/-- Weight of a pair: total `log p` over the primes of `P` identifying `x` and `y`. -/
def pairWeight (P : Finset ℕ) (x y : ℕ) : ℝ :=
  ∑ p ∈ P, if (x : ZMod p) = (y : ZMod p) then Real.log p else 0

theorem pairWeight_self (P : Finset ℕ) (x : ℕ) :
    pairWeight P x x = ∑ p ∈ P, Real.log p := by
  simp [pairWeight]

theorem pairWeight_le {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {X x y : ℕ}
    (hx : 1 ≤ x ∧ x ≤ X) (hy : 1 ≤ y ∧ y ≤ X) (hxy : x ≠ y) :
    pairWeight P x y ≤ Real.log X := by
  -- reduce to the case `x < y` by symmetry of the condition
  have key : ∀ u v : ℕ, u < v → 1 ≤ u → v ≤ X →
      pairWeight P u v ≤ Real.log X := by
    intro u v huv hu hv
    have hd : 0 < v - u := Nat.sub_pos_of_lt huv
    have hcong : ∀ p ∈ P, ((u : ZMod p) = (v : ZMod p) ↔ p ∣ v - u) := by
      intro p _
      rw [ZMod.natCast_eq_natCast_iff]
      exact Nat.modEq_iff_dvd' huv.le
    have h1 : pairWeight P u v = ∑ p ∈ P.filter (fun p => p ∣ v - u), Real.log p := by
      unfold pairWeight
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      by_cases h : p ∣ v - u
      · rw [if_pos ((hcong p hp).mpr h), if_pos h]
      · rw [if_neg (fun h' => h ((hcong p hp).mp h')), if_neg h]
    rw [h1]
    calc _ ≤ Real.log (v - u : ℕ) := sum_log_primes_dvd_le hP hd
      _ ≤ Real.log X := by
        apply Real.log_le_log (by exact_mod_cast hd)
        exact_mod_cast (le_trans (Nat.sub_le v u) hv)
  rcases lt_or_gt_of_ne hxy with h | h
  · exact key x y h hx.1 hy.2
  · have hsym : pairWeight P x y = pairWeight P y x := by
      unfold pairWeight
      refine Finset.sum_congr rfl (fun p _ => ?_)
      by_cases e : (x : ZMod p) = (y : ZMod p)
      · rw [if_pos e, if_pos e.symm]
      · rw [if_neg e, if_neg (fun e' => e e'.symm)]
    rw [hsym]
    exact key y x h hy.1 hx.2

/-- Cauchy–Schwarz on residue classes: `|T|² ≤ |Ω| * #{(x,y) ∈ T² : x ≡ y}`. -/
theorem card_sq_le_pairs (p : ℕ) (T : Finset ℕ) (Ω : Finset (ZMod p))
    (hT : ∀ n ∈ T, (n : ZMod p) ∈ Ω) :
    (T.card : ℝ) ^ 2 ≤ (Ω.card : ℝ) *
      ∑ x ∈ T, ∑ y ∈ T, (if (x : ZMod p) = (y : ZMod p) then (1 : ℝ) else 0) := by
  classical
  set N : ZMod p → ℝ := fun c => ((T.filter (fun n : ℕ => (n : ZMod p) = c)).card : ℝ) with hN
  have hJ : (T.card : ℝ) = ∑ c ∈ Ω, N c := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun n : ℕ => (n : ZMod p)) (t := Ω)
      (fun n hn => hT n hn)]
    push_cast
    rfl
  have hD : (∑ x ∈ T, ∑ y ∈ T, (if (x : ZMod p) = (y : ZMod p) then (1 : ℝ) else 0)) =
      ∑ c ∈ Ω, N c ^ 2 := by
    have h1 : ∀ x ∈ T, (∑ y ∈ T, (if (x : ZMod p) = (y : ZMod p) then (1 : ℝ) else 0)) =
        N (x : ZMod p) := by
      intro x _
      rw [hN]
      simp only
      rw [Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases e : (x : ZMod p) = (y : ZMod p)
      · rw [if_pos e, if_pos e.symm]
      · rw [if_neg e, if_neg (fun e' => e e'.symm)]
    rw [Finset.sum_congr rfl h1]
    rw [← Finset.sum_fiberwise_of_maps_to' (g := fun n : ℕ => (n : ZMod p)) (t := Ω)
      (fun n hn => hT n hn) N]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.sum_const, nsmul_eq_mul, hN]
    simp only
    ring
  rw [hD, hJ]
  exact sq_sum_le_card_mul_sum_sq

/-- **Gallagher's larger sieve.** -/
theorem larger_sieve {X : ℕ} (hX : 1 ≤ X) (T : Finset ℕ) (hT : ∀ n ∈ T, 1 ≤ n ∧ n ≤ X)
    (hTne : T.Nonempty) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Ω : (p : ℕ) → Finset (ZMod p)) (hTΩ : ∀ p ∈ P, ∀ n ∈ T, (n : ZMod p) ∈ Ω p)
    (ρ : ℕ → ℝ) (hρ : ∀ p ∈ P, 0 < ρ p) (hΩρ : ∀ p ∈ P, ((Ω p).card : ℝ) ≤ ρ p) :
    (T.card : ℝ) * (∑ p ∈ P, Real.log p / ρ p - Real.log X) ≤
      ∑ p ∈ P, Real.log p - Real.log X := by
  classical
  set J : ℝ := (T.card : ℝ) with hJdef
  have hJpos : 0 < J := by
    rw [hJdef]; exact_mod_cast hTne.card_pos
  set D : ℕ → ℝ := fun p =>
    ∑ x ∈ T, ∑ y ∈ T, (if (x : ZMod p) = (y : ZMod p) then (1 : ℝ) else 0) with hDdef
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX)
  -- Step 1: J² / ρ p ≤ D p
  have step1 : ∀ p ∈ P, J ^ 2 / ρ p ≤ D p := by
    intro p hp
    have h := card_sq_le_pairs p T (Ω p) (hTΩ p hp)
    have hD0 : 0 ≤ D p := by
      rw [hDdef]; simp only
      exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num))
    rw [div_le_iff₀ (hρ p hp)]
    calc J ^ 2 ≤ ((Ω p).card : ℝ) * D p := h
      _ ≤ ρ p * D p := mul_le_mul_of_nonneg_right (hΩρ p hp) hD0
      _ = D p * ρ p := mul_comm _ _
  -- Step 2: ∑ log p * D p ≤ J ∑ log p + J (J-1) log X
  have step2 : ∑ p ∈ P, Real.log p * D p ≤
      J * ∑ p ∈ P, Real.log p + J * (J - 1) * Real.log X := by
    have hswap : ∑ p ∈ P, Real.log p * D p = ∑ x ∈ T, ∑ y ∈ T, pairWeight P x y := by
      rw [hDdef]; simp only [pairWeight]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      refine Finset.sum_congr rfl (fun p _ => ?_)
      split_ifs <;> ring
    rw [hswap]
    have hrow : ∀ x ∈ T, ∑ y ∈ T, pairWeight P x y ≤
        ∑ p ∈ P, Real.log p + (J - 1) * Real.log X := by
      intro x hx
      rw [← Finset.add_sum_erase T _ hx, pairWeight_self]
      have hcard : ((T.erase x).card : ℝ) = J - 1 := by
        rw [Finset.card_erase_of_mem hx, hJdef]
        rw [Nat.cast_sub (Finset.card_pos.mpr ⟨x, hx⟩)]
        simp
      have : ∑ y ∈ T.erase x, pairWeight P x y ≤ ∑ _y ∈ T.erase x, Real.log X := by
        apply Finset.sum_le_sum
        intro y hy
        exact pairWeight_le hP (hT x hx) (hT y (Finset.mem_of_mem_erase hy))
          (fun e => (Finset.ne_of_mem_erase hy) e.symm)
      rw [Finset.sum_const, nsmul_eq_mul, hcard] at this
      linarith
    calc ∑ x ∈ T, ∑ y ∈ T, pairWeight P x y
        ≤ ∑ _x ∈ T, (∑ p ∈ P, Real.log p + (J - 1) * Real.log X) := Finset.sum_le_sum hrow
      _ = J * ∑ p ∈ P, Real.log p + J * (J - 1) * Real.log X := by
        rw [Finset.sum_const, nsmul_eq_mul, ← hJdef]; ring
  -- Step 3: combine
  have step3 : J ^ 2 * ∑ p ∈ P, Real.log p / ρ p ≤ ∑ p ∈ P, Real.log p * D p := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (hP p hp).one_lt.le)
    have := step1 p hp
    calc J ^ 2 * (Real.log p / ρ p) = Real.log p * (J ^ 2 / ρ p) := by ring
      _ ≤ Real.log p * D p := mul_le_mul_of_nonneg_left this hl
  have hfin : J * (J * ∑ p ∈ P, Real.log p / ρ p - ∑ p ∈ P, Real.log p - (J - 1) * Real.log X)
      ≤ 0 := by nlinarith [step2, step3]
  have hfin' : J * ∑ p ∈ P, Real.log p / ρ p - ∑ p ∈ P, Real.log p - (J - 1) * Real.log X ≤ 0 := by
    by_contra hc
    push_neg at hc
    have := mul_pos hJpos hc
    linarith
  nlinarith [hfin']

end Erdos374.D35

end
