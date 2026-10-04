import E374.D5Density

/-!
# `D5(X) ≍ X`

Counting `m = r P ∈ T5` (Chebyshev + even squarefree density + Abel summation) gives
`#T5(X) ≥ c₅ X` with `c₅ = log 2 / 40000`; removing the density-zero exceptional sets of
`T5_diff_D5_subset` gives `liminf D5(X)/X ≥ c₅ > 0`.

Inputs: RM, factorial growth, Harman at `θ = 11/100`, the project's uniform anchor sieve.
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

/-- Primes in `(y/4, y]`. -/
def quarterPrimes (y : ℕ) : Finset ℕ := (Finset.Ioc (y / 4) y).filter Nat.Prime

/-- Chebyshev: eventually `#quarterPrimes y ≥ (y/4) log 2 / log y`. -/
theorem quarterPrimes_card_ge :
    ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
      (y : ℝ) / 4 * Real.log 2 / Real.log y ≤ ((quarterPrimes y).card : ℝ) := by
  obtain ⟨N₁, hN₁⟩ := nat_eventually_rpow_log_dom (show (1 : ℝ) / 2 < 1 by norm_num)
    (16 / Real.log 2)
  refine ⟨max N₁ 3, fun y hy => ?_⟩
  have hy3 : 3 ≤ y := le_trans (le_max_right _ _) hy
  have hyR : (3 : ℝ) ≤ y := by exact_mod_cast hy3
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- θ(y) - θ(y/4)
  have hsplit : ∑ p ∈ primesUpTo y, Real.log p =
      ∑ p ∈ primesUpTo (y / 4), Real.log p + ∑ p ∈ quarterPrimes y, Real.log p := by
    unfold primesUpTo quarterPrimes
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
    exact (Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.div_le_self y 4)).symm
  have hθ := Chebyshev.theta_ge y
  rw [theta_eq_sum_primesUpTo] at hθ
  have hup := sum_log_primesUpTo_le (y / 4)
  have hy4 : ((y / 4 : ℕ) : ℝ) ≤ (y : ℝ) / 4 := Nat.cast_div_le
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have herr : Real.log (y + 1) + 2 * Real.sqrt y * Real.log y ≤ (y : ℝ) / 4 * Real.log 2 := by
    have h1 : Real.log (y + 1) ≤ 2 * Real.log y := by
      rw [← Real.log_rpow (by linarith)]
      apply Real.log_le_log (by linarith)
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; nlinarith
    have hs1 : 1 ≤ Real.sqrt y := by rw [Real.one_le_sqrt]; linarith
    have h2 := hN₁ y (le_trans (le_max_left _ _) hy)
    rw [Real.rpow_one, ← Real.sqrt_eq_rpow] at h2
    have : 16 / Real.log 2 * Real.sqrt y * Real.log y * Real.log 2 = 16 * Real.sqrt y * Real.log y := by
      field_simp
    have h3 : 16 * Real.sqrt y * Real.log y < y * Real.log 2 := by
      calc 16 * Real.sqrt y * Real.log y = (16 / Real.log 2 * Real.sqrt y * Real.log y) * Real.log 2 := by
            field_simp
        _ < y * Real.log 2 := mul_lt_mul_of_pos_right h2 hl2
    have hsl : 0 ≤ Real.sqrt y * Real.log y := by positivity
    nlinarith
  have hmass : (y : ℝ) / 4 * Real.log 2 ≤ ∑ p ∈ quarterPrimes y, Real.log p := by
    have h4 : Real.log 4 * ((y / 4 : ℕ) : ℝ) ≤ Real.log 4 * ((y : ℝ) / 4) :=
      mul_le_mul_of_nonneg_left hy4 (by positivity)
    rw [hlog4] at h4 hup
    linarith
  have hle : ∑ p ∈ quarterPrimes y, Real.log p ≤ ((quarterPrimes y).card : ℝ) * Real.log y := by
    calc ∑ p ∈ quarterPrimes y, Real.log p ≤ ∑ _p ∈ quarterPrimes y, Real.log y := by
          apply Finset.sum_le_sum
          intro p hp
          rw [quarterPrimes, Finset.mem_filter, Finset.mem_Ioc] at hp
          exact Real.log_le_log (by exact_mod_cast hp.2.pos) (by exact_mod_cast hp.1.2)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [div_le_iff₀ hlogy]
  linarith

/-- **`#T5(X) ≥ c₅ X` eventually**, with `c₅ = log 2 / 40000`. -/
theorem T5_count_ge :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X → Real.log 2 / 40000 * X ≤ (prefixCount T5 X : ℝ) := by
  classical
  obtain ⟨y₀, hy₀⟩ := quarterPrimes_card_ge
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- eventual comparisons
  obtain ⟨N₁, hN₁⟩ := nat_eventually_log_gt (4800 * (Real.log 8 / 24 + 1 / 24 + 2) + 1)
  obtain ⟨N₂, hN₂⟩ := nat_eventually_rpow_gt (show (0 : ℝ) < 99 / 100 by norm_num) (y₀ + 8)
  obtain ⟨N₃, hN₃⟩ := nat_eventually_rpow_dom (show (1 : ℝ) / 100 < 1 by norm_num) 9600
  obtain ⟨N₄, hN₄⟩ := nat_eventually_rpow_gt (show (0 : ℝ) < 1 / 100 by norm_num) 16
  refine ⟨max (max N₁ N₂) (max N₃ (max N₄ 2)), fun X hX => ?_⟩
  have hXN₁ : N₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXN₂ : N₂ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXN₃ : N₃ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXN₄ : N₄ ≤ X :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hX
  have hX2 : 2 ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hX
  have hX1R : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hX0R : (0 : ℝ) < X := by linarith
  have hlogX := hN₁ X hXN₁
  have hlogX0 : 0 < Real.log X := by
    have : (0 : ℝ) ≤ 4800 * (Real.log 8 / 24 + 1 / 24 + 2) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 8 by norm_num); positivity
    linarith
  set R : ℕ := ⌊(X : ℝ) ^ ((1 : ℝ) / 100) / 8⌋₊ with hR
  set Bset := (Finset.Icc 1 R).filter (fun r => r ∈ EvenSqf) with hBset
  set y : ℕ → ℕ := fun r => X / r with hy
  have hX99 := hN₂ X hXN₂
  have hX01 := hN₄ X hXN₄
  have hRle : (R : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 100) / 8 := Nat.floor_le (by positivity)
  -- for r ∈ Bset: `X/(4r) ≥ 2 X^{99/100}`
  have hXr : ∀ r ∈ Bset, 2 * (X : ℝ) ^ ((99 : ℝ) / 100) ≤ (X : ℝ) / (4 * r) := by
    intro r hr
    rw [hBset, Finset.mem_filter, Finset.mem_Icc] at hr
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr.1.1
    have hrR : (r : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 100) / 8 := le_trans (by exact_mod_cast hr.1.2) hRle
    rw [le_div_iff₀ (by positivity)]
    have : (X : ℝ) = (X : ℝ) ^ ((99 : ℝ) / 100) * (X : ℝ) ^ ((1 : ℝ) / 100) := by
      rw [← Real.rpow_add hX0R]; norm_num
    have h99 : 0 ≤ (X : ℝ) ^ ((99 : ℝ) / 100) := by positivity
    nlinarith
  -- primes `P > X^{99/100}` and `P > r`
  have hPbig : ∀ r ∈ Bset, ∀ P ∈ quarterPrimes (y r), (X : ℝ) ^ ((99 : ℝ) / 100) < P := by
    intro r hr P hP
    rw [quarterPrimes, Finset.mem_filter, Finset.mem_Ioc] at hP
    have h1 : (y r / 4 : ℕ) < P := hP.1.1
    have hr1 : 1 ≤ r := by rw [hBset, Finset.mem_filter, Finset.mem_Icc] at hr; exact hr.1.1
    have h2 : (X : ℝ) / r - 1 ≤ ((y r : ℕ) : ℝ) := by
      have := Nat.div_add_mod X r
      have hm := Nat.mod_lt X (show 0 < r by omega)
      have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
      have : (X : ℝ) = r * ((X / r : ℕ) : ℝ) + ((X % r : ℕ) : ℝ) := by exact_mod_cast this.symm
      have : ((X % r : ℕ) : ℝ) < r := by exact_mod_cast hm
      rw [div_sub_one hr0.ne', div_le_iff₀ hr0]
      simp only [hy]; nlinarith
    have h3 : ((y r : ℕ) : ℝ) / 4 - 1 ≤ ((y r / 4 : ℕ) : ℝ) := by
      have := Nat.div_add_mod (y r) 4
      have hm := Nat.mod_lt (y r) (show 0 < 4 by norm_num)
      have : ((y r : ℕ) : ℝ) = 4 * ((y r / 4 : ℕ) : ℝ) + ((y r % 4 : ℕ) : ℝ) := by
        exact_mod_cast this.symm
      have : ((y r % 4 : ℕ) : ℝ) < 4 := by exact_mod_cast hm
      linarith
    have h4 : ((y r / 4 : ℕ) : ℝ) + 1 ≤ P := by exact_mod_cast h1
    have h5 := hXr r hr
    have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have : (X : ℝ) / (4 * r) = ((X : ℝ) / r) / 4 := by field_simp
    have hX99' : (1 : ℝ) ≤ (X : ℝ) ^ ((99 : ℝ) / 100) := Real.one_le_rpow hX1R (by norm_num)
    linarith
  have hrP : ∀ r ∈ Bset, ∀ P ∈ quarterPrimes (y r), r < P := by
    intro r hr P hP
    have h1 := hPbig r hr P hP
    have hr' : (r : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 100) / 8 := by
      rw [hBset, Finset.mem_filter, Finset.mem_Icc] at hr
      exact le_trans (by exact_mod_cast hr.1.2) hRle
    have : (X : ℝ) ^ ((1 : ℝ) / 100) ≤ (X : ℝ) ^ ((99 : ℝ) / 100) :=
      Real.rpow_le_rpow_of_exponent_le hX1R (by norm_num)
    have : (0 : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 100) := by positivity
    have : (r : ℝ) < P := by linarith
    exact_mod_cast this
  -- the injection
  set Sg := Bset.sigma (fun r => quarterPrimes (y r)) with hSg
  have himg : Sg.image (fun x => x.1 * x.2) ⊆ (Finset.Icc 1 X).filter (fun m => m ∈ T5) := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨⟨r, P⟩, hx, rfl⟩ := hm
    show r * P ∈ (Finset.Icc 1 X).filter (fun m => m ∈ T5)
    rw [hSg, Finset.mem_sigma] at hx
    obtain ⟨hr, hP⟩ := hx
    simp only at hr hP
    have hPbig' := hPbig r hr P hP
    have hrP' := hrP r hr P hP
    have hr' := hr
    rw [hBset, Finset.mem_filter, Finset.mem_Icc] at hr'
    obtain ⟨⟨hr1, _⟩, hr2, hrsf⟩ := hr'
    have hP' := hP
    rw [quarterPrimes, Finset.mem_filter, Finset.mem_Ioc] at hP'
    obtain ⟨⟨_, hPy⟩, hPp⟩ := hP'
    have hmX : r * P ≤ X := by
      calc r * P ≤ r * (X / r) := Nat.mul_le_mul_left r hPy
        _ ≤ X := Nat.mul_div_le X r
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) hPp.ne_zero), hmX⟩, ?_, ?_, ?_⟩
    · rw [Nat.squarefree_mul_iff]
      refine ⟨?_, hrsf, hPp.prime.squarefree⟩
      exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hPp).mpr
        (fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega)))
    · exact dvd_mul_of_dvd_left hr2 P
    · show ((r * P : ℕ) : ℝ) ^ (1 - alpha) < (largestPrime (r * P) : ℝ)
      have hmem : P ∈ (r * P).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hPp, dvd_mul_left P r, mul_ne_zero (by omega) hPp.ne_zero⟩
      have hle : P ≤ largestPrime (r * P) := by
        unfold largestPrime
        exact le_trans (Finset.le_sup (f := id) hmem) (le_max_right _ _)
      have h1 : ((r * P : ℕ) : ℝ) ^ (1 - alpha) ≤ (X : ℝ) ^ ((99 : ℝ) / 100) := by
        rw [show (1 : ℝ) - alpha = 99 / 100 by norm_num [alpha]]
        exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hmX) (by norm_num)
      have : (P : ℝ) ≤ (largestPrime (r * P) : ℝ) := by exact_mod_cast hle
      linarith
  have hinj : Set.InjOn (fun x : (_ : ℕ) × ℕ => x.1 * x.2) (Sg : Set ((_ : ℕ) × ℕ)) := by
    rintro ⟨r, P⟩ h1 ⟨r', P'⟩ h2 heq
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, hSg] at h1 h2
    simp only at heq
    have hP : P.Prime := by
      have := h1.2; rw [quarterPrimes, Finset.mem_filter] at this; exact this.2
    have hP' : P'.Prime := by
      have := h2.2; rw [quarterPrimes, Finset.mem_filter] at this; exact this.2
    have hrP1 := hrP r h1.1 P h1.2
    have hrP2 := hrP r' h2.1 P' h2.2
    have hPmax : r' < P := by
      have := hPbig r h1.1 P h1.2
      have hr' : (r' : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 100) / 8 := by
        have := h2.1
        rw [hBset, Finset.mem_filter, Finset.mem_Icc] at this
        exact le_trans (by exact_mod_cast this.1.2) hRle
      have : (X : ℝ) ^ ((1 : ℝ) / 100) ≤ (X : ℝ) ^ ((99 : ℝ) / 100) :=
        Real.rpow_le_rpow_of_exponent_le hX1R (by norm_num)
      have : (0 : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 100) := by positivity
      have : (r' : ℝ) < P := by linarith
      exact_mod_cast this
    have hPdvd : P ∣ r' * P' := ⟨r, by rw [← heq]; ring⟩
    rcases (Nat.Prime.dvd_mul hP).mp hPdvd with hd | hd
    · have hr'1 : 1 ≤ r' := by
        have := h2.1; rw [hBset, Finset.mem_filter, Finset.mem_Icc] at this; exact this.1.1
      exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)
    · have hPP : P = P' := (Nat.prime_dvd_prime_iff_eq hP hP').mp hd
      subst hPP
      have : r = r' := Nat.eq_of_mul_eq_mul_right hP.pos heq
      subst this
      rfl
  have hcount : (Sg.card : ℝ) ≤ (prefixCount T5 X : ℝ) := by
    have := Finset.card_le_card himg
    rw [Finset.card_image_of_injOn hinj] at this
    unfold prefixCount; exact_mod_cast this
  -- lower bound for `Sg.card`
  have hsig : (Sg.card : ℝ) = ∑ r ∈ Bset, ((quarterPrimes (y r)).card : ℝ) := by
    rw [hSg, Finset.card_sigma]; push_cast; rfl
  have hper : ∀ r ∈ Bset, Real.log 2 / (4 * Real.log X) * ((X : ℝ) / r - 1) ≤
      ((quarterPrimes (y r)).card : ℝ) := by
    intro r hr
    have hr1 : 1 ≤ r := by rw [hBset, Finset.mem_filter, Finset.mem_Icc] at hr; exact hr.1.1
    have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have hyr : (X : ℝ) / r - 1 ≤ ((y r : ℕ) : ℝ) := by
      have := Nat.div_add_mod X r
      have hm := Nat.mod_lt X (show 0 < r by omega)
      have : (X : ℝ) = r * ((X / r : ℕ) : ℝ) + ((X % r : ℕ) : ℝ) := by exact_mod_cast this.symm
      have : ((X % r : ℕ) : ℝ) < r := by exact_mod_cast hm
      rw [div_sub_one hr0.ne', div_le_iff₀ hr0]
      simp only [hy]; nlinarith
    have hy0 : y₀ ≤ y r := by
      have h1 := hXr r hr
      have : ((y₀ : ℕ) : ℝ) + 8 < (X : ℝ) ^ ((99 : ℝ) / 100) := hX99
      have : (y₀ : ℝ) ≤ ((y r : ℕ) : ℝ) := by
        have : (X : ℝ) / (4 * r) = ((X : ℝ) / r) / 4 := by field_simp
        have : 0 ≤ (X : ℝ) ^ ((99 : ℝ) / 100) := by positivity
        linarith
      exact_mod_cast this
    have hq := hy₀ (y r) hy0
    have hyX : ((y r : ℕ) : ℝ) ≤ X := by exact_mod_cast Nat.div_le_self X r
    have hy1 : (2 : ℝ) ≤ ((y r : ℕ) : ℝ) := by
      have := hXr r hr
      have : (1 : ℝ) ≤ (X : ℝ) ^ ((99 : ℝ) / 100) := Real.one_le_rpow hX1R (by norm_num)
      have : (X : ℝ) / (4 * r) = ((X : ℝ) / r) / 4 := by field_simp
      linarith
    have hlogy : 0 < Real.log ((y r : ℕ) : ℝ) := Real.log_pos (by linarith)
    have hlogle : Real.log ((y r : ℕ) : ℝ) ≤ Real.log X := Real.log_le_log (by linarith) hyX
    calc Real.log 2 / (4 * Real.log X) * ((X : ℝ) / r - 1)
        ≤ Real.log 2 / (4 * Real.log X) * ((y r : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hyr (by positivity)
      _ ≤ ((y r : ℕ) : ℝ) / 4 * Real.log 2 / Real.log ((y r : ℕ) : ℝ) := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hlogy]
          have : 0 ≤ Real.log 2 * ((y r : ℕ) : ℝ) := by positivity
          nlinarith
      _ ≤ _ := hq
  -- Abel lower bound for `∑ 1/r`
  have habel := sum_inv_ge_of_density (B := EvenSqf) (c := 1 / 24) (c₀ := 2) (by norm_num)
    (by norm_num) (fun t => by have := card_evenSqf_ge t; linarith) R
  have hR1 : (X : ℝ) ^ ((1 : ℝ) / 100) / 8 ≤ (R : ℝ) + 1 := by
    have := Nat.lt_floor_add_one ((X : ℝ) ^ ((1 : ℝ) / 100) / 8); linarith
  have hlogR : (1 / 100) * Real.log X - Real.log 8 ≤ Real.log ((R : ℝ) + 1) := by
    have h1 : Real.log ((X : ℝ) ^ ((1 : ℝ) / 100) / 8) ≤ Real.log ((R : ℝ) + 1) :=
      Real.log_le_log (by positivity) hR1
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hX0R] at h1
    linarith
  have hsuminv : (1 / 4800) * Real.log X ≤ ∑ r ∈ Bset, (1 : ℝ) / r := by
    have : 1 / 24 * Real.log ((R : ℝ) + 1) - 1 / 24 - 2 ≤ ∑ r ∈ Bset, (1 : ℝ) / r := by
      rw [hBset]; push_cast at habel ⊢; exact habel
    have h2 : (1 / 4800) * Real.log X ≤ 1 / 24 * ((1 / 100) * Real.log X - Real.log 8) - 1 / 24 - 2 := by
      linarith
    linarith
  have hBcard : (Bset.card : ℝ) ≤ R := by
    have h : Bset.card ≤ R := by
      rw [hBset]
      exact le_trans (Finset.card_filter_le _ _) (by rw [Nat.card_Icc]; omega)
    exact_mod_cast h
  have htotal : Real.log 2 / (4 * Real.log X) * ((X : ℝ) * ((1 / 4800) * Real.log X) - R) ≤
      (Sg.card : ℝ) := by
    rw [hsig]
    calc Real.log 2 / (4 * Real.log X) * ((X : ℝ) * ((1 / 4800) * Real.log X) - R)
        ≤ Real.log 2 / (4 * Real.log X) * ((X : ℝ) * ∑ r ∈ Bset, (1 : ℝ) / r - Bset.card) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith
      _ = ∑ r ∈ Bset, Real.log 2 / (4 * Real.log X) * ((X : ℝ) / r - 1) := by
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
          congr 1
          refine Finset.sum_congr rfl (fun r _ => ?_)
          ring
      _ ≤ _ := Finset.sum_le_sum hper
  -- final arithmetic: `R ≤ X^{1/100}` is negligible
  have hRsmall : Real.log 2 / (4 * Real.log X) * R ≤ Real.log 2 / 19200 * X / 2 := by
    have h3 := hN₃ X hXN₃
    rw [Real.rpow_one] at h3
    have hlog1 : 1 ≤ Real.log X := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 8 by norm_num)
      linarith
    have : Real.log 2 / (4 * Real.log X) * R ≤ Real.log 2 / 4 * R := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num) (by nlinarith)
    have hRX : (R : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 100) := by
      have : (0 : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 100) := by positivity
      linarith
    have : Real.log 2 / 4 * R ≤ Real.log 2 / 19200 * X / 2 := by
      have hR9600 : (R : ℝ) * 9600 ≤ X := by
        have := mul_le_mul_of_nonneg_left hRX (by norm_num : (0 : ℝ) ≤ 9600)
        linarith
      have : Real.log 2 / 19200 * X / 2 = Real.log 2 / 4 * (X / 9600) := by ring
      rw [this]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    linarith
  have hmainterm : Real.log 2 / (4 * Real.log X) * ((X : ℝ) * ((1 / 4800) * Real.log X)) =
      Real.log 2 / 19200 * X := by
    field_simp; ring
  have : Real.log 2 / 19200 * X / 2 ≤ (Sg.card : ℝ) := by
    have := htotal
    rw [mul_sub, hmainterm] at this
    linarith
  have h40 : Real.log 2 / 40000 * X ≤ Real.log 2 / 19200 * X / 2 := by
    have : (0 : ℝ) ≤ Real.log 2 * X := by positivity
    nlinarith
  linarith

open Classical in
/-- **`D5(X) ≍ X`.** -/
theorem D5_order (hRM : Tasks.ValuationOneMass) (hG : Tasks.FactorialClassGrowth)
    (hH : AlmostAllShortPrimeIntervals theta) (hA : Tasks.UniformAnchorSieve) :
    PositiveLowerDensity D5 ∧ ∀ X : ℕ, prefixCount D5 X ≤ X := by
  obtain ⟨E, hE, N, hsub⟩ := T5_diff_D5_subset hRM hG hH
  have hbad : DensityZero (E ∪ (Initial N ∪ NonpairedFour alpha eta)) :=
    densityZero_union hE (densityZero_union (densityZero_initial N) (nonpairedFour_densityZero hA))
  obtain ⟨N₅, hN₅⟩ := T5_count_ge
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨⟨Real.log 2 / 40000, by positivity, fun ε hε => ?_⟩, fun X => ?_⟩
  · obtain ⟨N₁, hN₁⟩ := hbad ε hε
    refine ⟨max (max N₁ N₅) 1, fun X hX => ?_⟩
    have hX1 : N₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
    have hX5 : N₅ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
    have hX0 : 1 ≤ X := le_trans (le_max_right _ _) hX
    have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
    have hb := hN₁ X hX1
    rw [sub_zero, abs_of_nonneg (proportion_nonneg _ X)] at hb
    have hpart := prefixCount_partition D5 T5 X
    have hm1 : prefixCount (D5 ∩ T5) X ≤ prefixCount D5 X := prefixCount_mono Set.inter_subset_left X
    have hm2 : prefixCount (T5 \ D5) X ≤ prefixCount (E ∪ (Initial N ∪ NonpairedFour alpha eta)) X :=
      prefixCount_mono hsub X
    have hT := hN₅ X hX5
    unfold proportion at hb ⊢
    rw [div_lt_iff₀ hXR] at hb
    rw [le_div_iff₀ hXR]
    have e1 : (prefixCount (D5 ∩ T5) X : ℝ) + prefixCount (T5 \ D5) X = prefixCount T5 X := by
      exact_mod_cast hpart
    have e2 : (prefixCount (D5 ∩ T5) X : ℝ) ≤ prefixCount D5 X := by exact_mod_cast hm1
    have e3 : (prefixCount (T5 \ D5) X : ℝ) ≤
        prefixCount (E ∪ (Initial N ∪ NonpairedFour alpha eta)) X := by exact_mod_cast hm2
    nlinarith
  · unfold prefixCount
    calc _ ≤ (Finset.Icc 1 X).card := Finset.card_filter_le _ _
      _ = X := by simp

end Erdos374.D35

end
