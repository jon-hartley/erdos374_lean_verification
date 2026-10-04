import E374.Consecutive
import E374.Inputs

/-!
# D5: the five-factor construction and the exclusion of fewer factors

Family `T5 = {m : m squarefree, 2 ∣ m, P⁺(m) > m^{99/100}}` (original D6 parameters
`α = 1/100`, `θ = 11/100`, `η = 3/25`).

* `m = 2z` (`z ≥ 4`): `2! (z-1)! z! (2z-1)! (2z)! = (2z (z-1)! (2z-1)!)²`, so `F(m) ≤ 5`.
* Outside the Harman exceptional set the second-largest index is within `m^θ` of `m`;
  the large prime `P⁺(m)` then rules out 2- and 3-factor representations, RM (with `a = 0`)
  makes both gaps of a 4-factor representation `< m^η`, the paired case is impossible for
  squarefree `m`, and the remaining nonpaired case lies in `NonpairedFour alpha eta`,
  which has density zero by the project's `Tasks.UniformAnchorSieve`.
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

/-- The five-factor construction for even endpoints. -/
theorem hasRep_five_of_two_dvd {m : ℕ} (h2 : 2 ∣ m) (h8 : 8 ≤ m) : HasRep m 5 := by
  obtain ⟨z, rfl⟩ := h2
  have hz : 4 ≤ z := by omega
  refine hasRep_five_of (a := 2) (b := z - 1) (c := z) (d := 2 * z - 1) (by norm_num) (by omega)
    (by omega) (by omega) (by omega) ?_
  refine ⟨2 * z * (z - 1).factorial * (2 * z - 1).factorial, ?_⟩
  have e1 : z.factorial = z * (z - 1).factorial := by
    conv_lhs => rw [show z = (z - 1) + 1 by omega]
    rw [Nat.factorial_succ, show z - 1 + 1 = z by omega]
  have e2 : (2 * z).factorial = (2 * z) * (2 * z - 1).factorial := by
    conv_lhs => rw [show 2 * z = (2 * z - 1) + 1 by omega]
    rw [Nat.factorial_succ, show 2 * z - 1 + 1 = 2 * z by omega]
  rw [e1, e2, Nat.factorial_two]
  ring

/-- `v_p(m!) = 1` when `p ≤ m < 2p`. -/
theorem factorization_factorial_eq_one {p m : ℕ} (hp : p.Prime) (h1 : p ≤ m) (h2 : m < 2 * p) :
    (m.factorial).factorization p = 1 := by
  have hlog : Nat.log p m < 2 := by
    apply Nat.log_lt_of_lt_pow (by omega)
    have : 2 * p ≤ p ^ 2 := by nlinarith [hp.two_le]
    omega
  rw [Nat.factorization_factorial hp hlog]
  rw [show Finset.Ico 1 2 = ({1} : Finset ℕ) by decide, Finset.sum_singleton, pow_one]
  apply Nat.le_antisymm
  · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hp.pos).mpr (by omega))
  · exact (Nat.le_div_iff_mul_le hp.pos).mpr (by omega)

/-- If a factorial product `x! * m!` is a square and `p ≤ m < 2p`, then `p ≤ x`. -/
theorem le_of_isSquare_factorial_mul {p m x : ℕ} (hp : p.Prime) (h1 : p ≤ m) (h2 : m < 2 * p)
    (hs : IsSquare (x.factorial * m.factorial)) : p ≤ x := by
  by_contra hx
  push_neg at hx
  have := (Nat.isSquare_iff_even_factorization.mp hs) p hp
  rw [Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)] at this
  simp only [Finsupp.coe_add, Pi.add_apply, Nat.factorization_factorial_eq_zero_of_lt hx,
    factorization_factorial_eq_one hp h1 h2, zero_add] at this
  exact Nat.not_even_one this

/-- Valuation of a short block at a prime dividing its top element exactly once. -/
theorem falling_factorization_top {P ℓ m : ℕ} (hP : P.Prime) (hdvd : P ∣ m) (hsq : ¬ P ^ 2 ∣ m)
    (hℓ : 1 ≤ ℓ) (hℓP : ℓ ≤ P) (hℓm : ℓ ≤ m) : (falling ℓ m).factorization P = 1 := by
  have hne : ∀ i ∈ Finset.range ℓ, m - i ≠ 0 := by
    intro i hi; rw [Finset.mem_range] at hi; omega
  unfold falling
  rw [Nat.factorization_prod hne, Finsupp.finsetSum_apply]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (by omega : 0 < ℓ))]
  have h0 : (m - 0).factorization P = 1 := by
    rw [Nat.sub_zero]
    have hm0 : m ≠ 0 := by omega
    have hpos : 0 < m.factorization P := hP.factorization_pos_of_dvd hm0 hdvd
    have hlt : m.factorization P < 2 := by
      by_contra hc; push_neg at hc
      exact hsq ((hP.pow_dvd_iff_le_factorization hm0).mpr hc)
    omega
  have hrest : ∑ i ∈ (Finset.range ℓ).erase 0, (m - i).factorization P = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_erase, Finset.mem_range] at hi
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hd
    have hi0 : 0 < i := Nat.pos_of_ne_zero hi.1
    have : P ∣ i := by
      have h1 : P ∣ m - (m - i) := Nat.dvd_sub hdvd hd
      rwa [Nat.sub_sub_self (by omega)] at h1
    have := Nat.le_of_dvd hi0 this
    omega
  rw [h0, hrest]

/-- The family `T5`. -/
def T5 : Set ℕ := {m | Squarefree m ∧ 2 ∣ m ∧ LargePrime alpha m}

/-- The largest prime factor, when it exceeds 1, is a prime factor. -/
theorem largestPrime_mem {m : ℕ} (h : 1 < largestPrime m) : largestPrime m ∈ m.primeFactors := by
  unfold largestPrime at h ⊢
  rcases m.primeFactors.eq_empty_or_nonempty with he | hne
  · rw [he] at h; simp at h
  · obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup m.primeFactors hne id
    have : max 1 (m.primeFactors.sup id) = m.primeFactors.sup id := by
      apply max_eq_right
      rw [heq]; exact (Nat.prime_of_mem_primeFactors hi).one_lt.le
    rw [this, heq]; exact hi

/-- **Exclusion of 2-, 3- and 4-factor representations** on `T5`. -/
theorem T5_diff_D5_subset (hRM : Tasks.ValuationOneMass) (hG : Tasks.FactorialClassGrowth)
    (hH : AlmostAllShortPrimeIntervals theta) :
    ∃ E : Set ℕ, DensityZero E ∧ ∃ N : ℕ,
      T5 \ D5 ⊆ E ∪ (Initial N ∪ NonpairedFour alpha eta) := by
  obtain ⟨E, hE, NH, hNH⟩ := hH
  obtain ⟨N₀, hN₀⟩ := index_le_of_growth hG
  obtain ⟨X₀, hX₀⟩ := hRM eta (by norm_num [eta]) (by norm_num [eta])
  -- eventual comparisons
  -- (1) `m^θ < m/2`  (2) `m^θ < m^{99/100}`  (3) `N₀ + 3 m^θ log m < m^{99/100}`
  -- (4) `4096 m^θ log m < m^η`
  obtain ⟨N₁, hN₁⟩ := nat_eventually_rpow_dom (show theta < 1 by norm_num [theta]) 2
  obtain ⟨N₂, hN₂⟩ := nat_eventually_rpow_log_dom
    (show theta < 1 - alpha by norm_num [theta, alpha]) 6
  obtain ⟨N₃, hN₃⟩ := nat_eventually_rpow_dom (show (0 : ℝ) < 1 - alpha by norm_num [alpha])
    (2 * N₀)
  obtain ⟨N₄, hN₄⟩ := nat_eventually_rpow_log_dom (show theta < eta by norm_num [theta, eta]) 4096
  refine ⟨E, hE, max (max (max NH X₀) (max N₁ N₂)) (max (max N₃ N₄) 8), ?_⟩
  rintro m ⟨⟨hsf, h2, hLP⟩, hnot⟩
  by_contra hbad
  simp only [Set.mem_union, not_or] at hbad
  obtain ⟨hmE, hmI, hmNP⟩ := hbad
  have hmN : max (max (max NH X₀) (max N₁ N₂)) (max (max N₃ N₄) 8) ≤ m := by
    simp only [Initial, Set.mem_setOf_eq, not_lt] at hmI; exact hmI
  have hNHm : NH ≤ m := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hmN
  have hX₀m : X₀ ≤ m := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hmN
  have hN₁m : N₁ ≤ m := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hmN
  have hN₂m : N₂ ≤ m := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hmN
  have hN₃m : N₃ ≤ m := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_max_right _ _))) hmN
  have hN₄m : N₄ ≤ m := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_max_right _ _))) hmN
  have hm8 : 8 ≤ m := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hmN)
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hm0R : (0 : ℝ) < m := by linarith
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm1R
  -- the five-factor representation exists
  have h5 := hasRep_five_of_two_dvd h2 hm8
  -- so some k ∈ {2,3,4} has a representation
  have hk : ∃ k, 2 ≤ k ∧ k < 5 ∧ HasRep m k := by
    by_contra hc
    push_neg at hc
    exact hnot ⟨by omega, h5, fun k hk hk5 => hc k hk hk5⟩
  obtain ⟨k, hk2, hk5, hrep⟩ := hk
  -- Harman prime
  obtain ⟨p, hp, hpm, hgap⟩ := hNH m hNHm hmE
  have hθm : 2 * (m : ℝ) ^ theta < m := by
    have := hN₁ m hN₁m; rwa [Real.rpow_one] at this
  have hp2 : m < 2 * p := by
    have h : ((2 * (m - p) : ℕ) : ℝ) < m := by
      push_cast
      have : ((m - p : ℕ) : ℝ) = (m - p : ℕ) := rfl
      linarith
    have h' : 2 * (m - p) < m := by exact_mod_cast h
    omega
  -- the large prime P
  have hPgt : (m : ℝ) ^ (1 - alpha) < (largestPrime m : ℝ) := hLP
  have hP1 : 1 < largestPrime m := by
    have : (1 : ℝ) ≤ (m : ℝ) ^ (1 - alpha) := Real.one_le_rpow hm1R (by norm_num [alpha])
    exact_mod_cast (lt_of_le_of_lt this hPgt)
  set P := largestPrime m with hPdef
  have hPmem := largestPrime_mem hP1
  have hPp : P.Prime := Nat.prime_of_mem_primeFactors hPmem
  have hPdvd : P ∣ m := Nat.dvd_of_mem_primeFactors hPmem
  have hPsq : ¬ P ^ 2 ∣ m := by
    intro hd
    have := hsf P (by rw [← pow_two]; exact hd)
    exact hPp.one_lt.ne' (Nat.isUnit_iff.mp this)
  -- `m^θ < P`
  have hθP : (m : ℝ) ^ theta < P := by
    have : (m : ℝ) ^ theta ≤ (m : ℝ) ^ (1 - alpha) :=
      Real.rpow_le_rpow_of_exponent_le hm1R (by norm_num [theta, alpha])
    linarith
  -- second largest index bound: any index `x` with `x! m!`-type parity has `p ≤ x`
  have hgapP : ∀ x : ℕ, p ≤ x → x < m → (m - x : ℕ) < P ∧ ((m - x : ℕ) : ℝ) ≤ (m : ℝ) ^ theta := by
    intro x hpx hxm
    have h1 : ((m - x : ℕ) : ℝ) ≤ ((m - p : ℕ) : ℝ) := by exact_mod_cast (by omega : m - x ≤ m - p)
    refine ⟨?_, le_trans h1 hgap⟩
    have : ((m - x : ℕ) : ℝ) < P := lt_of_le_of_lt (le_trans h1 hgap) hθP
    exact_mod_cast this
  interval_cases k
  · -- two factors
    obtain ⟨d, hd1, hdm, hs⟩ := hasRep_two_iff.mp hrep
    have hpd := le_of_isSquare_factorial_mul hp hpm hp2 hs
    obtain ⟨hlP, _⟩ := hgapP d hpd hdm
    have hsq := (two_reduction hdm.le).mp hs
    have hv := falling_factorization_top hPp hPdvd hPsq (by omega) hlP.le (by omega)
    exact not_isSquare_of_factorization_one hPp (falling_ne_zero (by omega)) hv hsq
  · -- three factors
    obtain ⟨a, b, ha, hab, hbm, hs⟩ := hasRep_three_iff.mp hrep
    have hs' : IsSquare (b.factorial * m.factorial * a.factorial) := by
      have : b.factorial * m.factorial * a.factorial = a.factorial * b.factorial * m.factorial := by
        ring
      rw [this]; exact hs
    -- parity at p: a!, b! — b ≥ p
    have hpb : p ≤ b := by
      by_contra hb; push_neg at hb
      have := (Nat.isSquare_iff_even_factorization.mp hs) p hp
      rw [Nat.factorization_mul (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
        (Nat.factorial_ne_zero _), Nat.factorization_mul (Nat.factorial_ne_zero _)
        (Nat.factorial_ne_zero _)] at this
      simp only [Finsupp.coe_add, Pi.add_apply,
        Nat.factorization_factorial_eq_zero_of_lt (lt_trans hab hb),
        Nat.factorization_factorial_eq_zero_of_lt hb, factorization_factorial_eq_one hp hpm hp2,
        zero_add] at this
      exact Nat.not_even_one this
    obtain ⟨hlP, hlθ⟩ := hgapP b hpb hbm
    have hsq := (three_reduction hbm.le).mp hs
    -- a < P by growth
    have hidx := hN₀ m a (m - b) m (by omega) le_rfl (by omega) hsq
    have haP : a < P := by
      have h1 : (a : ℝ) ≤ N₀ + 3 * (m : ℝ) ^ theta * Real.log m := by
        have : 3 * ((m - b : ℕ) : ℝ) * Real.log m ≤ 3 * (m : ℝ) ^ theta * Real.log m := by
          apply mul_le_mul_of_nonneg_right _ hlogm; linarith
        linarith
      have h2 := hN₂ m hN₂m
      have h3 := hN₃ m hN₃m
      rw [Real.rpow_zero, mul_one] at h3
      have : (a : ℝ) < P := by linarith
      exact_mod_cast this
    have hq0 : (q a).factorization P = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (not_dvd_q_of_lt hPp haP)
    have hv := falling_factorization_top hPp hPdvd hPsq (by omega) hlP.le (by omega)
    have hv' : (q a * falling (m - b) m).factorization P = 1 := by
      rw [Nat.factorization_mul (q_ne_zero a) (falling_ne_zero (by omega))]
      simp only [Finsupp.coe_add, Pi.add_apply, hq0, hv, zero_add]
    exact not_isSquare_of_factorization_one hPp
      (mul_ne_zero (q_ne_zero a) (falling_ne_zero (by omega))) hv' hsq
  · -- four factors
    obtain ⟨b, c, d, hb, hbc, hcd, hdm, hs⟩ := hasRep_four_iff.mp hrep
    have hpd : p ≤ d := by
      by_contra hdp; push_neg at hdp
      have := (Nat.isSquare_iff_even_factorization.mp hs) p hp
      have hb0 := Nat.factorial_ne_zero b
      have hc0 := Nat.factorial_ne_zero c
      have hd0 := Nat.factorial_ne_zero d
      have hm0 := Nat.factorial_ne_zero m
      rw [Nat.factorization_mul (mul_ne_zero (mul_ne_zero hb0 hc0) hd0) hm0,
        Nat.factorization_mul (mul_ne_zero hb0 hc0) hd0, Nat.factorization_mul hb0 hc0] at this
      simp only [Finsupp.coe_add, Pi.add_apply,
        Nat.factorization_factorial_eq_zero_of_lt (lt_trans (lt_trans hbc hcd) hdp),
        Nat.factorization_factorial_eq_zero_of_lt (lt_trans hcd hdp),
        Nat.factorization_factorial_eq_zero_of_lt hdp, factorization_factorial_eq_one hp hpm hp2,
        zero_add] at this
      exact Nat.not_even_one this
    obtain ⟨hlP, hlθ⟩ := hgapP d hpd hdm
    have hsq := (four_reduction hbc.le hdm.le).mp hs
    -- the lower gap is `< m^η` by RM
    have hhη : ((c - b : ℕ) : ℝ) < (m : ℝ) ^ eta := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨R, hR0, hRsf, hRp, hRlog⟩ := hX₀ m 0 b c hX₀m (by omega) hbc (by omega) hcon
        (by simp; positivity)
      -- every prime of R divides `falling (m-d) m`
      have hRdvd : R ∣ falling (m - d) m := by
        rw [← Nat.prod_primeFactors_of_squarefree hRsf]
        apply Finset.prod_primes_dvd
        · intro p' hp'; exact (Nat.prime_of_mem_primeFactors hp').prime
        · intro p' hp'
          have hpp := Nat.prime_of_mem_primeFactors hp'
          obtain ⟨_, hv1⟩ := hRp p' hpp (Nat.dvd_of_mem_primeFactors hp')
          have hev := (Nat.isSquare_iff_even_factorization.mp hsq) p' hpp
          rw [Nat.factorization_mul (falling_ne_zero (by omega)) (falling_ne_zero (by omega))] at hev
          simp only [Finsupp.coe_add, Pi.add_apply, hv1] at hev
          have : (falling (m - d) m).factorization p' ≠ 0 := by
            intro h0; rw [h0] at hev; exact Nat.not_even_one hev
          exact Nat.dvd_of_factorization_pos this
      have hRle : R ≤ m ^ (m - d) :=
        le_trans (Nat.le_of_dvd (falling_pos (by omega)) hRdvd) (falling_le_pow _ _)
      have hlogR : Real.log R ≤ (m : ℝ) ^ theta * Real.log m := by
        have h1 : Real.log R ≤ Real.log ((m : ℝ) ^ (m - d)) := by
          apply Real.log_le_log (by exact_mod_cast hR0)
          exact_mod_cast hRle
        rw [Real.log_pow] at h1
        calc Real.log R ≤ ((m - d : ℕ) : ℝ) * Real.log m := h1
          _ ≤ (m : ℝ) ^ theta * Real.log m := mul_le_mul_of_nonneg_right hlθ hlogm
      have h4 := hN₄ m hN₄m
      linarith
    by_cases hpair : c - b = 1 ∧ m - d = 1
    · -- paired: `c * m` square, impossible for squarefree `m`
      have hcm : IsSquare (m * c) := by
        rw [hpair.1, hpair.2] at hsq
        simp only [falling, Finset.prod_range_one, Nat.sub_zero] at hsq
        rwa [mul_comm] at hsq
      have hdiv := hsf.dvd_of_isSquare_mul hcm
      have := Nat.le_of_dvd (by omega) hdiv
      omega
    · apply hmNP
      refine ⟨hLP, b, c, d, ⟨hb, hbc, hcd, hdm, (natSquare_iff_isSquare _).mpr hs⟩, ?_, hhη.le, ?_⟩
      · by_contra hc; push_neg at hc; exact hpair hc
      · exact le_trans hlθ (Real.rpow_le_rpow_of_exponent_le hm1R (by norm_num [theta, eta]))

/-- `NonpairedFour alpha eta` has density zero, from the project's anchor sieve. -/
theorem nonpairedFour_densityZero (hA : Tasks.UniformAnchorSieve) :
    DensityZero (NonpairedFour alpha eta) := by
  obtain ⟨C₄, _, _, _, N, hN⟩ := hA alpha eta (by norm_num [alpha]) (by norm_num [eta])
    (by norm_num [alpha, eta])
  obtain ⟨N₁, hN₁⟩ := nat_eventually_rpow_log_dom
    (show (1 : ℝ) / 2 + 3 * alpha / 2 + 3 * eta < 9 / 10 by norm_num [alpha, eta]) C₄
  refine densityZero_of_power_bound (C := 1) (δ := (9 : ℝ) / 10) (N := max N N₁) (by norm_num)
    (fun X hX => ?_)
  have h1 := (hN X (le_trans (le_max_left _ _) hX)).1
  have h2 := hN₁ X (le_trans (le_max_right _ _) hX)
  linarith

end Erdos374.D35

end
