import MomentResidualEven
import SingletonHarmonic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Choose.Sum

/-! Logarithmic coefficient energy for the fourth power of a bounded
integer Dirichlet polynomial. No unproved divisor-moment estimate is used. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators ArithmeticFunction.zeta
namespace FlatDivisorEnergyWork

def d (k n : ℕ) : ℕ := (ζ^k) n

theorem prime_power (k p e : ℕ) (hp : p.Prime) :
    d (k+1) (p^e) = (e+k).choose e := by
  induction k generalizing e with
  | zero => simp [d, hp.ne_zero]
  | succ k ih =>
    rw [d,pow_succ,ArithmeticFunction.mul_zeta_apply,Nat.sum_divisors_prime_pow hp]
    change (∑j∈Finset.range (e+1),d (k+1) (p^j)) = _
    calc
      _ = ∑j∈Finset.range (e+1),(j+k).choose k := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [ih, Nat.choose_symm_add]
      _ = (e+k+1).choose (k+1) := Nat.sum_range_add_choose e k
      _ = _ := by
        rw [Nat.add_assoc]
        exact Nat.choose_symm_add.symm

theorem choose_four_square (e : ℕ) :
    ((e+3).choose e)^2 ≤ (e+15).choose e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have h4 := Nat.add_one_mul_choose_eq (e+3) e
    have h16 := Nat.add_one_mul_choose_eq (e+15) e
    have hratio : (e+4)^2≤(e+16)*(e+1) := by nlinarith
    have hc := Nat.mul_le_mul hratio ih
    have h4sq := congrArg (fun n : ℕ => n^2) h4
    have h16mul := congrArg (fun n : ℕ => n*(e+1)) h16
    have hstep : ((e+4).choose (e+1))^2*(e+1)^2 ≤
        ((e+16).choose (e+1))*(e+1)^2 := by
      calc
        _ = (e+4)^2*((e+3).choose e)^2 := by nlinarith [h4sq]
        _ ≤ ((e+16)*(e+1))*((e+15).choose e) := hc
        _ = _ := by nlinarith [h16mul]
    exact (mul_le_mul_iff_left₀ (by positivity : 0<(e+1)^2)).mp hstep

theorem fourth_square_le (n : ℕ) : (d 4 n)^2≤d 16 n := by
  by_cases hn : n=0
  · simp [hn,d]
  have h4 : (ζ^4).IsMultiplicative := ArithmeticFunction.isMultiplicative_zeta.pow
  have h16 : (ζ^16).IsMultiplicative := ArithmeticFunction.isMultiplicative_zeta.pow
  unfold d
  rw [h4.multiplicative_factorization _ hn,h16.multiplicative_factorization _ hn]
  simp only [Finsupp.prod,←Finset.prod_pow]
  apply Finset.prod_le_prod
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors (by simpa using hp)
  change (d 4 (p^n.factorization p))^2≤d 16 (p^n.factorization p)
  rw [show 4=3+1 by norm_num,prime_power 3 p _ hpp,
    show 16=15+1 by norm_num,prime_power 15 p _ hpp]
  exact choose_four_square _

theorem coefficient_bound (f : ArithmeticFunction ℂ)
    (hf : ∀n,‖f n‖≤1) (k n : ℕ) : ‖(f^k) n‖≤d k n := by
  induction k generalizing n with
  | zero => by_cases hn : n=1 <;> simp [hn,d]
  | succ k ih =>
    rw [pow_succ,ArithmeticFunction.mul_apply]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑p∈n.divisorsAntidiagonal,(d k p.1:ℝ)*ζ p.2 := by
        apply Finset.sum_le_sum
        intro p hp
        rw [norm_mul,ArithmeticFunction.zeta_apply_ne
          (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp),Nat.cast_one,mul_one]
        exact (mul_le_mul (ih p.1) (hf p.2) (norm_nonneg _)
          (Nat.cast_nonneg _)).trans_eq (by ring)
      _ = _ := by simp [d,pow_succ,ArithmeticFunction.mul_apply]

theorem sum_bound (k L : ℕ) :
    (∑n∈Finset.Ioc 0 L,(d (k+1) n:ℝ))≤(L:ℝ)*(1+Real.log L)^k := by
  induction k generalizing L with
  | zero =>
    simp only [d,pow_one,pow_zero,mul_one]
    calc
      _ = ∑_n∈Finset.Ioc 0 L,(1:ℝ) := Finset.sum_congr rfl (by
        intro n hn
        simp [ArithmeticFunction.zeta_apply_ne (ne_of_gt (Finset.mem_Ioc.mp hn).1)])
      _ ≤ (L:ℝ) := by simp
  | succ k ih =>
    by_cases hL : L=0
    · simp [hL]
    have hL1 : (1:ℝ)≤L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hL
    have hlog : 0≤Real.log L := Real.log_nonneg hL1
    have he : (∑n∈Finset.Ioc 0 L,d (k+1+1) n) =
        ∑m∈Finset.Ioc 0 L,∑n∈Finset.Ioc 0 (L/m),d (k+1) n := by
      simp only [d,pow_succ']
      rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [ArithmeticFunction.zeta_apply_ne (ne_of_gt (Finset.mem_Ioc.mp hm).1),one_mul]
    have heR : (∑n∈Finset.Ioc 0 L,(d (k+1+1) n:ℝ)) =
        ∑m∈Finset.Ioc 0 L,∑n∈Finset.Ioc 0 (L/m),(d (k+1) n:ℝ) := by
      exact_mod_cast he
    rw [heR]
    calc
      _ ≤ ∑m∈Finset.Ioc 0 L,((L:ℝ)/m)*(1+Real.log L)^k := by
        apply Finset.sum_le_sum
        intro m hm
        have hm0 := (Finset.mem_Ioc.mp hm).1
        have hmL := (Finset.mem_Ioc.mp hm).2
        have hquot : 1≤L/m := (Nat.le_div_iff_mul_le hm0).mpr (by simpa using hmL)
        have hquotR : (1:ℝ)≤(L/m:ℕ) := by exact_mod_cast hquot
        have hlq : Real.log (L/m:ℕ)≤Real.log L :=
          Real.log_le_log (by linarith) (by exact_mod_cast Nat.div_le_self L m)
        have hdiv : ((L/m:ℕ):ℝ)≤(L:ℝ)/m := by
          apply (le_div_iff₀ (by exact_mod_cast hm0 : (0:ℝ)<m)).mpr
          exact_mod_cast Nat.div_mul_le_self L m
        apply (ih (L/m)).trans
        exact mul_le_mul hdiv
          (pow_le_pow_left₀ (by linarith [Real.log_nonneg hquotR]) (by linarith) k)
          (by positivity) (by positivity)
      _ = (L:ℝ)*(1+Real.log L)^k*SingletonHarmonic.harmonicSum L := by
        rw [SingletonHarmonic.harmonicSum,Finset.mul_sum]
        have heq : Finset.Ioc 0 L=Finset.Icc 1 L := by ext n; simp; omega
        rw [heq]
        apply Finset.sum_congr rfl
        intro m hm
        ring
      _ ≤ (L:ℝ)*(1+Real.log L)^k*(1+Real.log L) :=
        mul_le_mul_of_nonneg_left (SingletonHarmonic.harmonicSum_le_one_add_log L)
          (by positivity)
      _ = _ := by rw [pow_succ]; ring

theorem fourth_energy (f : ArithmeticFunction ℂ) (hf : ∀n,‖f n‖≤1) (L : ℕ) :
    (∑n∈Finset.Ioc 0 L,‖(f^4) n‖^2)≤(L:ℝ)*(1+Real.log L)^15 := by
  calc
    _ ≤ ∑n∈Finset.Ioc 0 L,(d 16 n:ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hh := pow_le_pow_left₀ (norm_nonneg _) (coefficient_bound f hf 4 n) 2
      exact hh.trans (by exact_mod_cast fourth_square_le n)
    _ ≤ _ := sum_bound 15 L

run_cmd do
  for decl in [``prime_power, ``choose_four_square, ``fourth_square_le,
      ``coefficient_bound, ``sum_bound, ``fourth_energy] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end FlatDivisorEnergyWork
