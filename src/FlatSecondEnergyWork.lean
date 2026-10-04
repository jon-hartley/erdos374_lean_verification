import FlatDivisorEnergyWork
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators ArithmeticFunction.zeta
namespace FlatSecondEnergyWork
open FlatDivisorEnergyWork
theorem choose_two_square (e : ℕ) :
    ((e+1).choose e)^2 ≤ (e+3).choose e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have htwo := Nat.add_one_mul_choose_eq (e+1) e
    have hfour := Nat.add_one_mul_choose_eq (e+3) e
    have hratio : (e+2)^2≤(e+4)*(e+1) := by nlinarith
    have hc := Nat.mul_le_mul hratio ih
    have htwosq := congrArg (fun n : ℕ => n^2) htwo
    have hfourmul := congrArg (fun n : ℕ => n*(e+1)) hfour
    have hstep : ((e+2).choose (e+1))^2*(e+1)^2 ≤
        ((e+4).choose (e+1))*(e+1)^2 := by
      calc
        _ = (e+2)^2*((e+1).choose e)^2 := by nlinarith [htwosq]
        _ ≤ ((e+4)*(e+1))*((e+3).choose e) := hc
        _ = _ := by nlinarith [hfourmul]
    exact (mul_le_mul_iff_left₀ (by positivity : 0<(e+1)^2)).mp hstep

theorem second_square_le (n : ℕ) : (d 2 n)^2≤d 4 n := by
  by_cases hn : n=0
  · simp [hn,d]
  have htwo : (ζ^2).IsMultiplicative := ArithmeticFunction.isMultiplicative_zeta.pow
  have hfour : (ζ^4).IsMultiplicative := ArithmeticFunction.isMultiplicative_zeta.pow
  unfold d
  rw [htwo.multiplicative_factorization _ hn,hfour.multiplicative_factorization _ hn]
  simp only [Finsupp.prod,←Finset.prod_pow]
  apply Finset.prod_le_prod
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors (by simpa using hp)
  change (d 2 (p^n.factorization p))^2≤d 4 (p^n.factorization p)
  rw [show 2=1+1 by norm_num,prime_power 1 p _ hpp,
    show 4=3+1 by norm_num,prime_power 3 p _ hpp]
  exact choose_two_square _

theorem second_energy (f : ArithmeticFunction ℂ) (hf : ∀n,‖f n‖≤1) (L : ℕ) :
    (∑n∈Finset.Ioc 0 L,‖(f^2) n‖^2)≤(L:ℝ)*(1+Real.log L)^3 := by
  calc
    _ ≤ ∑n∈Finset.Ioc 0 L,(d 4 n:ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hh := pow_le_pow_left₀ (norm_nonneg _) (coefficient_bound f hf 2 n) 2
      exact hh.trans (by exact_mod_cast second_square_le n)
    _ ≤ _ := sum_bound 3 L

run_cmd do
  for decl in [``choose_two_square, ``second_square_le, ``second_energy] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end FlatSecondEnergyWork
