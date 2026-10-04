import E374.ESet
import E374.LargerSieve
import E374.Mertens
import E374.WeilCount

/-!
# Large-kernel fibres via Gallagher's larger sieve

For fixed `(a, h)` the fibre `T = fibre X a h` is sieved by
* the primes `p > h` dividing `q_a` (each confines `n` to `h` residues), and
* an auxiliary set `P2` of primes larger than `a, h`, with residue sets `Ω2 p`.
`fibre_bound_generic` packages the larger-sieve inequality; it is then specialised to
the trivial residue sets (no analytic input) and to the Weil square-residue sets.
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

/-- Primes `p > h` dividing `q_a`. -/
def bigPrimesOfQ (a h : ℕ) : Finset ℕ := (q a).primeFactors.filter (fun p => h < p)

theorem log_q_eq_sum (a : ℕ) : Real.log (q a) = ∑ p ∈ (q a).primeFactors, Real.log p := by
  rw [log_eq_sum_factorization (q_ne_zero a) (subset_refl _)]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Nat.factorization_eq_one_of_squarefree (squarefree_q a) (Nat.prime_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hp)]
  simp

theorem sum_log_bigPrimes_ge (a h : ℕ) :
    Real.log (q a) - Real.log 4 * h ≤ ∑ p ∈ bigPrimesOfQ a h, Real.log p := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (q a).primeFactors (fun p => h < p)
    (fun p => Real.log (p : ℝ))
  have hsmall : ∑ p ∈ (q a).primeFactors.filter (fun p => ¬ h < p), Real.log (p : ℝ) ≤
      Real.log 4 * h := by
    calc _ ≤ ∑ p ∈ primesUpTo h, Real.log (p : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            rw [Finset.mem_filter] at hp
            rw [mem_primesUpTo]
            exact ⟨Nat.prime_of_mem_primeFactors hp.1, by omega⟩
          · intro p hp _
            exact Real.log_nonneg (by exact_mod_cast (mem_primesUpTo.mp hp).1.one_lt.le)
      _ ≤ _ := sum_log_primesUpTo_le h
  rw [log_q_eq_sum, ← hsplit]
  unfold bigPrimesOfQ
  linarith

theorem sum_log_bigPrimes_le (a h : ℕ) :
    ∑ p ∈ bigPrimesOfQ a h, Real.log p ≤ Real.log 4 * a := by
  calc _ ≤ ∑ p ∈ primesUpTo a, Real.log (p : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [bigPrimesOfQ, Finset.mem_filter] at hp
          have hpp := Nat.prime_of_mem_primeFactors hp.1
          rw [mem_primesUpTo]
          exact ⟨hpp, le_of_prime_dvd_q hpp (Nat.dvd_of_mem_primeFactors hp.1)⟩
        · intro p hp _
          exact Real.log_nonneg (by exact_mod_cast (mem_primesUpTo.mp hp).1.one_lt.le)
    _ ≤ _ := sum_log_primesUpTo_le a

/-- Residues of fibre elements modulo a big prime of `q_a`. -/
theorem fibre_mod_bigPrime {X a h n p : ℕ} (hn : n ∈ fibre X a h) (hp : p ∈ bigPrimesOfQ a h) :
    (n : ZMod p) ∈ (Finset.range h).image (fun i : ℕ => (i : ZMod p)) := by
  rw [fibre, Finset.mem_filter] at hn
  obtain ⟨_, hahn, hs⟩ := hn
  rw [bigPrimesOfQ, Finset.mem_filter] at hp
  have hpp := Nat.prime_of_mem_primeFactors hp.1
  have hdq : p ∣ q a := Nat.dvd_of_mem_primeFactors hp.1
  have hdf : p ∣ falling h n := dvd_trans hdq (q_dvd_of_isSquare hs)
  unfold falling at hdf
  obtain ⟨i, hi, hdi⟩ := (Prime.dvd_finset_prod_iff hpp.prime _).mp hdf
  rw [Finset.mem_image]
  refine ⟨i, hi, ?_⟩
  have hin : i ≤ n := by rw [Finset.mem_range] at hi; omega
  have h0 : ((n - i : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdi
  rw [Nat.cast_sub hin, sub_eq_zero] at h0
  exact h0.symm

/-- **Generic large-kernel inequality** from the larger sieve. -/
theorem fibre_bound_generic {X a h : ℕ} (hX : 1 ≤ X) (hh : 1 ≤ h) (P2 : Finset ℕ)
    (hP2 : ∀ p ∈ P2, p.Prime ∧ a < p ∧ h < p) (Ω2 : (p : ℕ) → Finset (ZMod p))
    (hΩ2 : ∀ p ∈ P2, ∀ n ∈ fibre X a h, (n : ZMod p) ∈ Ω2 p) (ρ2 : ℕ → ℝ)
    (hρ2 : ∀ p ∈ P2, 0 < ρ2 p ∧ ((Ω2 p).card : ℝ) ≤ ρ2 p) :
    ((fibre X a h).card : ℝ) *
        ((Real.log (q a) - Real.log 4 * h) / h + ∑ p ∈ P2, Real.log p / ρ2 p - Real.log X) ≤
      max (Real.log 4 * a + ∑ p ∈ P2, Real.log p - Real.log X) 0 := by
  classical
  rcases (fibre X a h).eq_empty_or_nonempty with hT | hT
  · rw [hT]; simp
  set P1 := bigPrimesOfQ a h with hP1
  have hdisj : Disjoint P1 P2 := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [hP1, bigPrimesOfQ, Finset.mem_filter] at hp1
    have hpp := Nat.prime_of_mem_primeFactors hp1.1
    have := le_of_prime_dvd_q hpp (Nat.dvd_of_mem_primeFactors hp1.1)
    have := (hP2 p hp2).2.1
    omega
  set Ω : (p : ℕ) → Finset (ZMod p) := fun p =>
    if p ∈ P1 then (Finset.range h).image (fun i : ℕ => (i : ZMod p)) else Ω2 p with hΩ
  set ρ : ℕ → ℝ := fun p => if p ∈ P1 then (h : ℝ) else ρ2 p with hρ
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hPprime : ∀ p ∈ P1 ∪ P2, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h1 | h2
    · rw [hP1, bigPrimesOfQ, Finset.mem_filter] at h1
      exact Nat.prime_of_mem_primeFactors h1.1
    · exact (hP2 p h2).1
  have hmem : ∀ p ∈ P1 ∪ P2, ∀ n ∈ fibre X a h, (n : ZMod p) ∈ Ω p := by
    intro p hp n hn
    rw [hΩ]
    by_cases h1 : p ∈ P1
    · simp only [if_pos h1]; exact fibre_mod_bigPrime hn h1
    · simp only [if_neg h1]
      exact hΩ2 p ((Finset.mem_union.mp hp).resolve_left h1) n hn
  have hρpos : ∀ p ∈ P1 ∪ P2, 0 < ρ p := by
    intro p hp
    rw [hρ]
    by_cases h1 : p ∈ P1
    · simp only [if_pos h1]; exact hhR
    · simp only [if_neg h1]; exact (hρ2 p ((Finset.mem_union.mp hp).resolve_left h1)).1
  have hΩρ : ∀ p ∈ P1 ∪ P2, ((Ω p).card : ℝ) ≤ ρ p := by
    intro p hp
    rw [hρ, hΩ]
    by_cases h1 : p ∈ P1
    · simp only [if_pos h1]
      have := Finset.card_image_le (s := Finset.range h) (f := fun i : ℕ => (i : ZMod p))
      rw [Finset.card_range] at this
      exact_mod_cast this
    · simp only [if_neg h1]; exact (hρ2 p ((Finset.mem_union.mp hp).resolve_left h1)).2
  have hT1 : ∀ n ∈ fibre X a h, 1 ≤ n ∧ n ≤ X := by
    intro n hn
    rw [fibre, Finset.mem_filter, Finset.mem_Icc] at hn
    exact hn.1
  have hLS := larger_sieve hX (fibre X a h) hT1 hT (P1 ∪ P2) hPprime Ω hmem ρ hρpos hΩρ
  have hS : ∑ p ∈ P1 ∪ P2, Real.log p / ρ p =
      (∑ p ∈ P1, Real.log p) / h + ∑ p ∈ P2, Real.log p / ρ2 p := by
    rw [Finset.sum_union hdisj, Finset.sum_div]
    congr 1
    · refine Finset.sum_congr rfl (fun p hp => ?_)
      rw [hρ]; simp only [if_pos hp]
    · refine Finset.sum_congr rfl (fun p hp => ?_)
      have : p ∉ P1 := Finset.disjoint_right.mp hdisj hp
      rw [hρ]; simp only [if_neg this]
  have hL : ∑ p ∈ P1 ∪ P2, Real.log p = ∑ p ∈ P1, Real.log p + ∑ p ∈ P2, Real.log p :=
    Finset.sum_union hdisj
  rw [hS, hL] at hLS
  have hlow := sum_log_bigPrimes_ge a h
  have hup := sum_log_bigPrimes_le a h
  have hdiv : (Real.log (q a) - Real.log 4 * h) / h ≤ (∑ p ∈ P1, Real.log p) / h :=
    div_le_div_of_nonneg_right hlow hhR.le
  have hJ : (0 : ℝ) ≤ (fibre X a h).card := Nat.cast_nonneg _
  calc ((fibre X a h).card : ℝ) *
        ((Real.log (q a) - Real.log 4 * h) / h + ∑ p ∈ P2, Real.log p / ρ2 p - Real.log X)
      ≤ ((fibre X a h).card : ℝ) *
        ((∑ p ∈ P1, Real.log p) / h + ∑ p ∈ P2, Real.log p / ρ2 p - Real.log X) := by
        apply mul_le_mul_of_nonneg_left _ hJ; linarith
    _ ≤ ∑ p ∈ P1, Real.log p + ∑ p ∈ P2, Real.log p - Real.log X := hLS
    _ ≤ Real.log 4 * a + ∑ p ∈ P2, Real.log p - Real.log X := by linarith
    _ ≤ _ := le_max_left _ _

/-- Auxiliary primes in `(Y, Q]`. -/
def auxPrimes (Y Q : ℕ) : Finset ℕ := (Finset.Ioc Y Q).filter Nat.Prime

theorem sum_log_auxPrimes_le (Y Q : ℕ) : ∑ p ∈ auxPrimes Y Q, Real.log p ≤ Real.log 4 * Q := by
  calc _ ≤ ∑ p ∈ primesUpTo Q, Real.log (p : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [auxPrimes, Finset.mem_filter, Finset.mem_Ioc] at hp
          rw [mem_primesUpTo]; exact ⟨hp.2, hp.1.2⟩
        · intro p hp _
          exact Real.log_nonneg (by exact_mod_cast (mem_primesUpTo.mp hp).1.one_lt.le)
    _ ≤ _ := sum_log_primesUpTo_le Q

/-- All residues, as a finset defined for every modulus. -/
def allRes (p : ℕ) : Finset (ZMod p) := (Finset.range p).image (fun z : ℕ => (z : ZMod p))

theorem mem_allRes {p : ℕ} (hp : 0 < p) (n : ℕ) : (n : ZMod p) ∈ allRes p := by
  rw [allRes, Finset.mem_image]
  exact ⟨n % p, Finset.mem_range.mpr (Nat.mod_lt n hp), ZMod.natCast_mod n p⟩

theorem card_allRes_le (p : ℕ) : (allRes p).card ≤ p := by
  rw [allRes]; exact le_trans Finset.card_image_le (by rw [Finset.card_range])

theorem allRes_eq_univ {p : ℕ} [NeZero p] : allRes p = Finset.univ := by
  ext z
  simp only [Finset.mem_univ, iff_true, allRes, Finset.mem_image, Finset.mem_range]
  exact ⟨z.val, ZMod.val_lt z, ZMod.natCast_zmod_val z⟩

/-- **Large-kernel fibre, trivial residue sets** (no Weil input). -/
theorem fibre_bound_trivial {X a h Y Q : ℕ} (hX : 1 ≤ X) (hh : 1 ≤ h) (haY : a < Y + 1)
    (hhY : h < Y + 1) (CM : ℝ)
    (hM : Real.log Q - Real.log Y - CM ≤ ∑ p ∈ auxPrimes Y Q, Real.log p / p) :
    ((fibre X a h).card : ℝ) *
        ((Real.log (q a) - Real.log 4 * h) / h + (Real.log Q - Real.log Y - CM) - Real.log X) ≤
      max (Real.log 4 * a + Real.log 4 * Q - Real.log X) 0 := by
  have hP2 : ∀ p ∈ auxPrimes Y Q, p.Prime ∧ a < p ∧ h < p := by
    intro p hp
    rw [auxPrimes, Finset.mem_filter, Finset.mem_Ioc] at hp
    exact ⟨hp.2, by omega, by omega⟩
  have hgen := fibre_bound_generic hX hh (auxPrimes Y Q) hP2 (fun p => allRes p)
    (fun p hp n _ => mem_allRes (hP2 p hp).1.pos n) (fun p => (p : ℝ)) (by
      intro p hp
      have hpp := (hP2 p hp).1
      refine ⟨by exact_mod_cast hpp.pos, ?_⟩
      exact_mod_cast card_allRes_le p)
  have hJ : (0 : ℝ) ≤ (fibre X a h).card := Nat.cast_nonneg _
  have hup := sum_log_auxPrimes_le Y Q
  calc ((fibre X a h).card : ℝ) *
        ((Real.log (q a) - Real.log 4 * h) / h + (Real.log Q - Real.log Y - CM) - Real.log X)
      ≤ ((fibre X a h).card : ℝ) *
        ((Real.log (q a) - Real.log 4 * h) / h + ∑ p ∈ auxPrimes Y Q, Real.log p / p -
          Real.log X) := by
        apply mul_le_mul_of_nonneg_left _ hJ; linarith
    _ ≤ max (Real.log 4 * a + ∑ p ∈ auxPrimes Y Q, Real.log p - Real.log X) 0 := hgen
    _ ≤ _ := max_le_max (by linarith) le_rfl

open Classical in
/-- Weil residue sets. -/
def weilSet (a h p : ℕ) : Finset (ZMod p) :=
  (allRes p).filter (fun z : ZMod p =>
    IsSquare ((q a : ZMod p) * ∏ i ∈ Finset.range h, (z - (i : ZMod p))))

theorem fibre_mem_weilSet {X a h n p : ℕ} (hp : 0 < p) (hn : n ∈ fibre X a h) :
    (n : ZMod p) ∈ weilSet a h p := by
  classical
  rw [fibre, Finset.mem_filter] at hn
  obtain ⟨_, hahn, hs⟩ := hn
  rw [weilSet, Finset.mem_filter]
  refine ⟨mem_allRes hp n, ?_⟩
  have hmap := hs.map (Nat.castRingHom (ZMod p))
  have hcast : (Nat.castRingHom (ZMod p)) (q a * falling h n) =
      (q a : ZMod p) * ∏ i ∈ Finset.range h, ((n : ZMod p) - (i : ZMod p)) := by
    rw [map_mul, falling, map_prod]
    congr 1
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    simp only [eq_natCast]
    rw [Nat.cast_sub (by omega)]
  rwa [hcast] at hmap

theorem card_weilSet_le (hW : CoarseWeilBound) {a h p : ℕ} (hp : p.Prime) (hap : a < p)
    (hhp : h < p) (hh : 2 ≤ h) :
    ((weilSet a h p).card : ℝ) ≤ ((p : ℝ) + h + 5 * h * Real.sqrt p) / 2 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  set U : Finset (ZMod p) := (Finset.range h).image (fun i : ℕ => (i : ZMod p)) with hU
  have hinj : Set.InjOn (fun i : ℕ => (i : ZMod p)) (Finset.range h : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    simp only at hij
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      at hij
    exact hij
  have hUcard : U.card = h := by
    rw [hU, Finset.card_image_of_injOn hinj, Finset.card_range]
  have hUne : U.Nonempty := by
    rw [← Finset.card_pos, hUcard]; omega
  have hprod : ∀ z : ZMod p, ∏ i ∈ Finset.range h, (z - (i : ZMod p)) = ∏ u ∈ U, (z - u) := by
    intro z
    rw [hU, Finset.prod_image hinj]
  have hc : (q a : ZMod p) ≠ 0 := by
    intro h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    exact not_dvd_q_of_lt hp hap h0
  have hset : weilSet a h p =
      Finset.univ.filter (fun z : ZMod p => IsSquare ((q a : ZMod p) * ∏ u ∈ U, (z - u))) := by
    rw [weilSet, allRes_eq_univ]
    congr 1
    funext z
    rw [hprod z]
  have := square_count_le hW hp hp2 (q a : ZMod p) hc U hUne
  rw [hset]
  convert this using 2 <;> simp [hUcard]

/-- **Large-kernel fibre, Weil residue sets.** -/
theorem fibre_bound_weil (hW : CoarseWeilBound) {X a h Y Q : ℕ} (hX : 1 ≤ X) (hh : 2 ≤ h)
    (haY : a < Y + 1) (hhY : h < Y + 1) :
    ((fibre X a h).card : ℝ) *
        ((Real.log (q a) - Real.log 4 * h) / h +
          ∑ p ∈ auxPrimes Y Q, Real.log p / (((p : ℝ) + h + 5 * h * Real.sqrt p) / 2) -
          Real.log X) ≤
      max (Real.log 4 * a + Real.log 4 * Q - Real.log X) 0 := by
  have hP2 : ∀ p ∈ auxPrimes Y Q, p.Prime ∧ a < p ∧ h < p := by
    intro p hp
    rw [auxPrimes, Finset.mem_filter, Finset.mem_Ioc] at hp
    exact ⟨hp.2, by omega, by omega⟩
  have hgen := fibre_bound_generic hX (by omega) (auxPrimes Y Q) hP2 (fun p => weilSet a h p)
    (fun p hp n hn => fibre_mem_weilSet (hP2 p hp).1.pos hn)
    (fun p => ((p : ℝ) + h + 5 * h * Real.sqrt p) / 2) (by
      intro p hp
      obtain ⟨hpp, hap, hhp⟩ := hP2 p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      refine ⟨by positivity, card_weilSet_le hW hpp hap hhp hh⟩)
  have hup := sum_log_auxPrimes_le Y Q
  exact le_trans hgen (max_le_max (by linarith) le_rfl)

end Erdos374.D35

end
