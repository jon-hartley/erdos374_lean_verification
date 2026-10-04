import E374.Core

/-!
# Erdős 374, D3/D5 extension — basic square-class algebra

`D3` and `D5` are defined in exactly the style of the project's `D6`.
This module proves the elementary square-class facts used throughout:
the squarefree-kernel parity identity, `q a` squarefree with `q a ∣ a!`,
the factorial/falling-product reductions for two, three and four factors,
and explicit constructors/destructors for representations.
Everything here is unconditional.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators
open Finset

namespace Erdos374

/-- `F(m) = 3`, in the style of the project's `D6`. -/
def D3 : Set ℕ := {m | 1 < m ∧ HasRep m 3 ∧ ¬ HasRep m 2}

/-- `F(m) = 5`, in the style of the project's `D6`. -/
def D5 : Set ℕ :=
  {m | 1 < m ∧ HasRep m 5 ∧ ∀ k : ℕ, 2 ≤ k → k < 5 → ¬ HasRep m k}

namespace D35

/-! ## Squares -/

theorem natSquare_iff_isSquare (n : ℕ) : NatSquare n ↔ IsSquare n := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, by ring⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, by ring⟩

theorem isSquare_iff_of_parity {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → m.factorization p % 2 = n.factorization p % 2) :
    IsSquare m ↔ IsSquare n := by
  rw [Nat.isSquare_iff_even_factorization, Nat.isSquare_iff_even_factorization]
  refine forall_congr' fun p => imp_congr_right fun hp => ?_
  rw [Nat.even_iff, Nat.even_iff, h p hp]

theorem isSquare_sq_mul_iff {y x : ℕ} (hy : y ≠ 0) :
    IsSquare (y * y * x) ↔ IsSquare x := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  have hyy : y * y ≠ 0 := mul_ne_zero hy hy
  refine isSquare_iff_of_parity (mul_ne_zero hyy hx.ne') hx.ne' fun p _ => ?_
  rw [Nat.factorization_mul hyy hx.ne', Nat.factorization_mul hy hy]
  simp only [Finsupp.coe_add, Pi.add_apply]
  omega

theorem isSquare_of_mul_sq {y x : ℕ} (hy : y ≠ 0) (h : IsSquare (y * y * x)) :
    IsSquare x := (isSquare_sq_mul_iff hy).mp h

/-! ## The squarefree kernel `sf` -/

theorem sf_ne_zero (n : ℕ) : sf n ≠ 0 := by
  unfold sf
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero

theorem sf_pos (n : ℕ) : 0 < sf n := Nat.pos_of_ne_zero (sf_ne_zero n)

theorem sf_factorization (n p : ℕ) :
    (sf n).factorization p =
      if p ∈ n.primeFactors.filter (fun p => n.factorization p % 2 = 1) then 1 else 0 := by
  unfold sf
  rw [Nat.factorization_prod (fun x hx =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hx).1).ne_zero)]
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (fun x hx => by
    rw [(Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hx).1).factorization,
      Finsupp.single_apply])]
  exact Finset.sum_ite_eq' _ _ _

theorem sf_factorization_le_one (n p : ℕ) : (sf n).factorization p ≤ 1 := by
  rw [sf_factorization]
  split_ifs <;> omega

theorem squarefree_sf (n : ℕ) : Squarefree (sf n) :=
  Nat.squarefree_of_factorization_le_one (sf_ne_zero n) (sf_factorization_le_one n)

/-- The parity identity: `sf n` has the same factorization parities as `n`. -/
theorem sf_factorization_mod_two (n p : ℕ) :
    (sf n).factorization p % 2 = n.factorization p % 2 := by
  rw [sf_factorization]
  split_ifs with h
  · exact ((Finset.mem_filter.mp h).2).symm
  · by_cases ho : n.factorization p % 2 = 1
    · exfalso
      apply h
      refine Finset.mem_filter.mpr ⟨?_, ho⟩
      have hne : n.factorization p ≠ 0 := by omega
      rw [← Nat.support_factorization]
      exact Finsupp.mem_support_iff.mpr hne
    · omega

theorem sf_factorization_le (n p : ℕ) : (sf n).factorization p ≤ n.factorization p := by
  have h1 := sf_factorization_le_one n p
  have h2 := sf_factorization_mod_two n p
  omega

theorem sf_dvd {n : ℕ} (hn : n ≠ 0) : sf n ∣ n :=
  (Nat.factorization_le_iff_dvd (sf_ne_zero n) hn).mp
    (fun p => sf_factorization_le n p)

theorem isSquare_sf_mul_iff {n : ℕ} (hn : n ≠ 0) (m : ℕ) :
    IsSquare (sf n * m) ↔ IsSquare (n * m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  refine isSquare_iff_of_parity (mul_ne_zero (sf_ne_zero n) hm.ne')
    (mul_ne_zero hn hm.ne') fun p _ => ?_
  rw [Nat.factorization_mul (sf_ne_zero n) hm.ne', Nat.factorization_mul hn hm.ne']
  simp only [Finsupp.coe_add, Pi.add_apply]
  have := sf_factorization_mod_two n p
  omega

/-! ## The factorial kernels `q a` -/

theorem q_ne_zero (a : ℕ) : q a ≠ 0 := sf_ne_zero _

theorem q_zero' : q 0 = 1 := by simp [q, sf]

theorem q_one' : q 1 = 1 := by simp [q, sf]

theorem q_pos (a : ℕ) : 0 < q a := sf_pos _

theorem squarefree_q (a : ℕ) : Squarefree (q a) := squarefree_sf _

theorem q_dvd_factorial (a : ℕ) : q a ∣ a.factorial := sf_dvd (Nat.factorial_ne_zero a)

theorem isSquare_q_mul_iff (a m : ℕ) :
    IsSquare (q a * m) ↔ IsSquare (a.factorial * m) :=
  isSquare_sf_mul_iff (Nat.factorial_ne_zero a) m

/-- Every prime divisor of `q a` is at most `a`. -/
theorem le_of_prime_dvd_q {a p : ℕ} (hp : p.Prime) (h : p ∣ q a) : p ≤ a :=
  (Nat.Prime.dvd_factorial hp).mp (dvd_trans h (q_dvd_factorial a))

/-- A prime larger than `a` does not divide `q a`. -/
theorem not_dvd_q_of_lt {a p : ℕ} (hp : p.Prime) (h : a < p) : ¬ p ∣ q a :=
  fun hd => absurd (le_of_prime_dvd_q hp hd) (by omega)

/-- If `q a * m` is a square with `m ≠ 0`, then `q a ∣ m`. -/
theorem q_dvd_of_isSquare {a m : ℕ} (h : IsSquare (q a * m)) : q a ∣ m :=
  (squarefree_q a).dvd_of_isSquare_mul h

/-! ## Falling products -/

theorem falling_eq_descFactorial (h c : ℕ) : falling h c = c.descFactorial h := by
  rw [falling, Nat.descFactorial_eq_prod_range]

theorem falling_pos {h c : ℕ} (hhc : h ≤ c) : 0 < falling h c := by
  rw [falling_eq_descFactorial]
  exact Nat.descFactorial_pos.mpr hhc

theorem falling_one' (c : ℕ) : falling 1 c = c := by simp [falling]

theorem falling_ne_zero {h c : ℕ} (hhc : h ≤ c) : falling h c ≠ 0 :=
  (falling_pos hhc).ne'

/-- `c! = b! * P_{c-b}(c)` for `b ≤ c`. -/
theorem factorial_eq_mul_falling {b c : ℕ} (hbc : b ≤ c) :
    c.factorial = b.factorial * falling (c - b) c := by
  rw [falling_eq_descFactorial]
  have h := Nat.factorial_mul_descFactorial (Nat.sub_le c b)
  rw [Nat.sub_sub_self hbc] at h
  exact h.symm

/-- `P_h(c) ≤ c^h`. -/
theorem falling_le_pow (h c : ℕ) : falling h c ≤ c ^ h := by
  unfold falling
  calc ∏ i ∈ Finset.range h, (c - i) ≤ ∏ _i ∈ Finset.range h, c :=
        Finset.prod_le_prod (fun i _ => Nat.sub_le c i)
    _ = c ^ h := by simp

/-! ## Square-class reductions -/

theorem two_reduction {d n : ℕ} (hdn : d ≤ n) :
    IsSquare (d.factorial * n.factorial) ↔ IsSquare (falling (n - d) n) := by
  rw [factorial_eq_mul_falling hdn, ← mul_assoc]
  exact isSquare_sq_mul_iff (Nat.factorial_ne_zero d)

theorem three_reduction {a b n : ℕ} (hbn : b ≤ n) :
    IsSquare (a.factorial * b.factorial * n.factorial) ↔
      IsSquare (q a * falling (n - b) n) := by
  rw [isSquare_q_mul_iff, factorial_eq_mul_falling hbn]
  have : a.factorial * b.factorial * (b.factorial * falling (n - b) n) =
      b.factorial * b.factorial * (a.factorial * falling (n - b) n) := by ring
  rw [this]
  exact isSquare_sq_mul_iff (Nat.factorial_ne_zero b)

theorem four_reduction {b c d n : ℕ} (hbc : b ≤ c) (hdn : d ≤ n) :
    IsSquare (b.factorial * c.factorial * d.factorial * n.factorial) ↔
      IsSquare (falling (c - b) c * falling (n - d) n) := by
  rw [factorial_eq_mul_falling hbc, factorial_eq_mul_falling hdn]
  have : b.factorial * (b.factorial * falling (c - b) c) * d.factorial *
        (d.factorial * falling (n - d) n) =
      (b.factorial * d.factorial) * (b.factorial * d.factorial) *
        (falling (c - b) c * falling (n - d) n) := by ring
  rw [this]
  exact isSquare_sq_mul_iff (mul_ne_zero (Nat.factorial_ne_zero b) (Nat.factorial_ne_zero d))

/-! ## Representations -/

theorem hasRep_two_iff {m : ℕ} :
    HasRep m 2 ↔ ∃ d, 1 ≤ d ∧ d < m ∧ IsSquare (d.factorial * m.factorial) := by
  constructor
  · rintro ⟨_, ⟨r⟩⟩
    have he : r.index (1 : Fin 2) = m := r.endpoint 1 (by norm_num)
    have hs : NatSquare ((r.index 0).factorial * (r.index 1).factorial) := by
      simpa [Fin.prod_univ_succ] using r.square
    refine ⟨r.index 0, r.positive 0, ?_, ?_⟩
    · simpa [he] using r.increasing (by decide : (0 : Fin 2) < 1)
    · rw [← natSquare_iff_isSquare]; simpa [he] using hs
  · rintro ⟨d, hd, hdm, hs⟩
    refine ⟨by decide, ⟨{
      index := ![d, m]
      increasing := ?_
      positive := ?_
      endpoint := ?_
      square := ?_ }⟩⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all <;> omega
    · intro i
      fin_cases i <;> simp_all <;> omega
    · intro i hi
      fin_cases i <;> simp_all
    · rw [natSquare_iff_isSquare]
      simpa [Fin.prod_univ_succ] using hs

theorem hasRep_three_iff {m : ℕ} :
    HasRep m 3 ↔ ∃ a b, 1 ≤ a ∧ a < b ∧ b < m ∧
      IsSquare (a.factorial * b.factorial * m.factorial) := by
  constructor
  · rintro ⟨_, ⟨r⟩⟩
    have he : r.index (2 : Fin 3) = m := r.endpoint 2 (by norm_num)
    have hs : NatSquare ((r.index 0).factorial * (r.index 1).factorial *
        (r.index 2).factorial) := by
      simpa [Fin.prod_univ_succ, mul_assoc] using r.square
    refine ⟨r.index 0, r.index 1, r.positive 0,
      r.increasing (by decide : (0 : Fin 3) < 1), ?_, ?_⟩
    · simpa [he] using r.increasing (by decide : (1 : Fin 3) < 2)
    · rw [← natSquare_iff_isSquare]; simpa [he] using hs
  · rintro ⟨a, b, ha, hab, hbm, hs⟩
    refine ⟨by decide, ⟨{
      index := ![a, b, m]
      increasing := ?_
      positive := ?_
      endpoint := ?_
      square := ?_ }⟩⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all <;> omega
    · intro i
      fin_cases i <;> simp_all <;> omega
    · intro i hi
      fin_cases i <;> simp_all
    · rw [natSquare_iff_isSquare]
      simpa [Fin.prod_univ_succ, mul_assoc] using hs

theorem hasRep_four_iff {m : ℕ} :
    HasRep m 4 ↔ ∃ b c d, 1 ≤ b ∧ b < c ∧ c < d ∧ d < m ∧
      IsSquare (b.factorial * c.factorial * d.factorial * m.factorial) := by
  constructor
  · rintro ⟨_, ⟨r⟩⟩
    have he : r.index (3 : Fin 4) = m := r.endpoint 3 (by norm_num)
    have hs : NatSquare ((r.index 0).factorial * (r.index 1).factorial *
        (r.index 2).factorial * (r.index 3).factorial) := by
      simpa [Fin.prod_univ_succ, mul_assoc] using r.square
    refine ⟨r.index 0, r.index 1, r.index 2, r.positive 0,
      r.increasing (by decide : (0 : Fin 4) < 1),
      r.increasing (by decide : (1 : Fin 4) < 2), ?_, ?_⟩
    · simpa [he] using r.increasing (by decide : (2 : Fin 4) < 3)
    · rw [← natSquare_iff_isSquare]; simpa [he] using hs
  · rintro ⟨b, c, d, hb, hbc, hcd, hdm, hs⟩
    refine ⟨by decide, ⟨{
      index := ![b, c, d, m]
      increasing := ?_
      positive := ?_
      endpoint := ?_
      square := ?_ }⟩⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all <;> omega
    · intro i
      fin_cases i <;> simp_all <;> omega
    · intro i hi
      fin_cases i <;> simp_all
    · rw [natSquare_iff_isSquare]
      simpa [Fin.prod_univ_succ, mul_assoc] using hs

theorem hasRep_five_of {a b c d m : ℕ} (ha : 1 ≤ a) (hab : a < b) (hbc : b < c)
    (hcd : c < d) (hdm : d < m)
    (hs : IsSquare (a.factorial * b.factorial * c.factorial * d.factorial * m.factorial)) :
    HasRep m 5 := by
  refine ⟨by decide, ⟨{
    index := ![a, b, c, d, m]
    increasing := ?_
    positive := ?_
    endpoint := ?_
    square := ?_ }⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> omega
  · intro i
    fin_cases i <;> simp_all <;> omega
  · intro i hi
    fin_cases i <;> simp_all
  · rw [natSquare_iff_isSquare]
    simpa [Fin.prod_univ_succ, mul_assoc] using hs

/-! ## Reduced characterizations -/

/-- Two factors: `m` has a 2-representation iff some block `P_ℓ(m)` with `1 ≤ ℓ < m`
is a square. -/
theorem hasRep_two_iff_falling {m : ℕ} :
    HasRep m 2 ↔ ∃ ℓ, 1 ≤ ℓ ∧ ℓ < m ∧ IsSquare (falling ℓ m) := by
  rw [hasRep_two_iff]
  constructor
  · rintro ⟨d, hd, hdm, hs⟩
    refine ⟨m - d, by omega, by omega, (two_reduction hdm.le).mp hs⟩
  · rintro ⟨ℓ, hℓ, hℓm, hs⟩
    refine ⟨m - ℓ, by omega, by omega, (two_reduction (by omega)).mpr ?_⟩
    rwa [Nat.sub_sub_self hℓm.le]

/-- Three factors in reduced form: `a ≥ 1`, block length `h ≥ 1`, and `a + h < m`. -/
theorem hasRep_three_iff_reduced {m : ℕ} :
    HasRep m 3 ↔ ∃ a h, 1 ≤ a ∧ 1 ≤ h ∧ a + h < m ∧ IsSquare (q a * falling h m) := by
  rw [hasRep_three_iff]
  constructor
  · rintro ⟨a, b, ha, hab, hbm, hs⟩
    exact ⟨a, m - b, ha, by omega, by omega, (three_reduction hbm.le).mp hs⟩
  · rintro ⟨a, h, ha, hh, hahm, hs⟩
    refine ⟨a, m - h, ha, by omega, by omega, (three_reduction (by omega)).mpr ?_⟩
    rwa [Nat.sub_sub_self (by omega : h ≤ m)]

/-- A square `m ≥ 2` has a two-factor representation `(m-1)! m!`. -/
theorem hasRep_two_of_square {m : ℕ} (hm : 2 ≤ m) (hs : IsSquare m) : HasRep m 2 := by
  rw [hasRep_two_iff_falling]
  exact ⟨1, le_refl 1, by omega, by simpa [falling] using hs⟩

end D35

end Erdos374

end
