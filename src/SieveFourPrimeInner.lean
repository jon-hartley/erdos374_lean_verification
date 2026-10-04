import SieveRosser
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! A tuple from the four-prime inner box satisfies the actual lower Rosser
cubic prefix tests. We use the inner cutoff D^(1/(1+s^9)) explicitly.
No identification with a later printed cutoff, a constant raw-box selector,
or the full source coefficient decomposition is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace SieveFourPrimeInner

theorem inner_pair_power_bound (D q a1 a2 : ℝ)
    (hD : 0 ≤ D) (hq : 0 < q) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (hinner : a1*a2^3 < D^(1/q)) :
    a1^q * (a2^q)^3 < D := by
  have hpow : (a1*a2^3)^q < D :=
    (Real.lt_rpow_inv_iff_of_pos (by positivity) hD hq).mp (by simpa only [one_div] using hinner)
  simpa only [Real.mul_rpow ha1 (pow_nonneg ha2 3),
    ← Real.rpow_pow_comm ha2 q 3] using hpow

theorem inner_four_power_bound (D q a1 a2 a3 a4 : ℝ)
    (hD : 0 ≤ D) (hq : 0 < q)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3) (ha4 : 0 ≤ a4)
    (hinner : a1*a2*a3*a4^3 < D^(1/q)) :
    a1^q*a2^q*a3^q*(a4^q)^3 < D := by
  have hpow : (a1*a2*a3*a4^3)^q < D :=
    (Real.lt_rpow_inv_iff_of_pos (by positivity) hD hq).mp (by simpa only [one_div] using hinner)
  simpa only [Real.mul_rpow (mul_nonneg (mul_nonneg ha1 ha2) ha3) (pow_nonneg ha4 3),
    Real.mul_rpow (mul_nonneg ha1 ha2) ha3, Real.mul_rpow ha1 ha2,
    ← Real.rpow_pow_comm ha4 q 3] using hpow

/-- The numerical implication is stronger than the prime case: it holds for
every natural tuple with the specified half-open box memberships. -/
theorem inner_tests (D s a1 a2 a3 a4 : ℝ) (p1 p2 p3 p4 : ℕ)
    (hD : 1 < D) (hs : 0 ≤ s)
    (ha1 : 1 ≤ a1) (ha2 : 1 ≤ a2) (ha3 : 1 ≤ a3) (ha4 : 1 ≤ a4)
    (hpair : a1*a2^3 < D^(1/(1+s^9)))
    (hfour : a1*a2*a3*a4^3 < D^(1/(1+s^9)))
    (hp1 : a1 ≤ (p1 : ℝ) ∧ (p1 : ℝ) < a1^(1+s^9))
    (hp2 : a2 ≤ (p2 : ℝ) ∧ (p2 : ℝ) < a2^(1+s^9))
    (hp3 : a3 ≤ (p3 : ℝ) ∧ (p3 : ℝ) < a3^(1+s^9))
    (hp4 : a4 ≤ (p4 : ℝ) ∧ (p4 : ℝ) < a4^(1+s^9)) :
    ((p1*p2^3 : ℕ) : ℝ) < D ∧ ((p1*p2*p3*p4^3 : ℕ) : ℝ) < D := by
  have hD0 : 0 ≤ D := by linarith
  have hq : 0 < 1+s^9 := by positivity
  have ha10 : 0 ≤ a1 := by linarith
  have ha20 : 0 ≤ a2 := by linarith
  have ha30 : 0 ≤ a3 := by linarith
  have ha40 : 0 ≤ a4 := by linarith
  have hb2 : (p2 : ℝ)^3 ≤ (a2^(1+s^9))^3 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hp2.2.le 3
  have hb4 : (p4 : ℝ)^3 ≤ (a4^(1+s^9))^3 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hp4.2.le 3
  constructor
  · have hle : (p1 : ℝ)*(p2 : ℝ)^3 ≤ a1^(1+s^9)*(a2^(1+s^9))^3 :=
      mul_le_mul hp1.2.le hb2 (by positivity) (Real.rpow_nonneg ha10 _)
    have hlt := hle.trans_lt
      (inner_pair_power_bound D (1+s^9) a1 a2 hD0 hq ha10 ha20 hpair)
    simpa only [Nat.cast_mul, Nat.cast_pow] using hlt
  · have h12 : (p1 : ℝ)*(p2 : ℝ) ≤ a1^(1+s^9)*a2^(1+s^9) :=
      mul_le_mul hp1.2.le hp2.2.le (Nat.cast_nonneg _) (Real.rpow_nonneg ha10 _)
    have h123 : (p1 : ℝ)*(p2 : ℝ)*(p3 : ℝ) ≤
        a1^(1+s^9)*a2^(1+s^9)*a3^(1+s^9) :=
      mul_le_mul h12 hp3.2.le (Nat.cast_nonneg _) (by positivity)
    have hle : (p1 : ℝ)*(p2 : ℝ)*(p3 : ℝ)*(p4 : ℝ)^3 ≤
        a1^(1+s^9)*a2^(1+s^9)*a3^(1+s^9)*(a4^(1+s^9))^3 :=
      mul_le_mul h123 hb4 (by positivity) (by positivity)
    have hlt := hle.trans_lt
      (inner_four_power_bound D (1+s^9) a1 a2 a3 a4 hD0 hq ha10 ha20 ha30 ha40 hfour)
    simpa only [Nat.cast_mul, Nat.cast_pow] using hlt

theorem accepts_inner (D s a1 a2 a3 a4 : ℝ) (p1 p2 p3 p4 : ℕ)
    (hD : 1 < D) (hs : 0 ≤ s)
    (ha1 : 1 ≤ a1) (ha2 : 1 ≤ a2) (ha3 : 1 ≤ a3) (ha4 : 1 ≤ a4)
    (hpair : a1*a2^3 < D^(1/(1+s^9)))
    (hfour : a1*a2*a3*a4^3 < D^(1/(1+s^9)))
    (hp1 : a1 ≤ (p1 : ℝ) ∧ (p1 : ℝ) < a1^(1+s^9))
    (hp2 : a2 ≤ (p2 : ℝ) ∧ (p2 : ℝ) < a2^(1+s^9))
    (hp3 : a3 ≤ (p3 : ℝ) ∧ (p3 : ℝ) < a3^(1+s^9))
    (hp4 : a4 ≤ (p4 : ℝ) ∧ (p4 : ℝ) < a4^(1+s^9)) :
    SievePrefix.accepts (SieveRosser.cubicGate D) false 1 [p1,p2,p3,p4] :=
  (SieveRosser.lower_four_tests D p1 p2 p3 p4).mpr
    (inner_tests D s a1 a2 a3 a4 p1 p2 p3 p4 hD hs ha1 ha2 ha3 ha4
      hpair hfour hp1 hp2 hp3 hp4)

/-- Acceptance also gives membership in the actual selector of any ambient
list in which the tuple occurs as a sublist. -/
theorem selected_inner_of_sublist (D s a1 a2 a3 a4 : ℝ) (p1 p2 p3 p4 : ℕ)
    (hD : 1 < D) (hs : 0 ≤ s)
    (ha1 : 1 ≤ a1) (ha2 : 1 ≤ a2) (ha3 : 1 ≤ a3) (ha4 : 1 ≤ a4)
    (hpair : a1*a2^3 < D^(1/(1+s^9)))
    (hfour : a1*a2*a3*a4^3 < D^(1/(1+s^9)))
    (hp1 : a1 ≤ (p1 : ℝ) ∧ (p1 : ℝ) < a1^(1+s^9))
    (hp2 : a2 ≤ (p2 : ℝ) ∧ (p2 : ℝ) < a2^(1+s^9))
    (hp3 : a3 ≤ (p3 : ℝ) ∧ (p3 : ℝ) < a3^(1+s^9))
    (hp4 : a4 ≤ (p4 : ℝ) ∧ (p4 : ℝ) < a4^(1+s^9))
    (ps : List ℕ) (hsub : [p1,p2,p3,p4].Sublist ps) :
    [p1,p2,p3,p4].toFinset ∈ SieveRosser.selected D false ps :=
  SievePrefix.selected_of_sublist_accepts (SieveRosser.cubicGate D) false 1 ps
    [p1,p2,p3,p4] hsub
    (accepts_inner D s a1 a2 a3 a4 p1 p2 p3 p4 hD hs ha1 ha2 ha3 ha4
      hpair hfour hp1 hp2 hp3 hp4)

#print axioms accepts_inner
#print axioms selected_inner_of_sublist
run_cmd do
  for decl in [``inner_pair_power_bound, ``inner_four_power_bound, ``inner_tests,
      ``accepts_inner, ``selected_inner_of_sublist] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
run_cmd Lean.logInfo "SIEVE_FOUR_PRIME_INNER_PASSED; INNER CUTOFF ONLY; NO FULL BOXING IDENTIFICATION"

end SieveFourPrimeInner
end
