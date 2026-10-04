import FourPrimeSourceScales
import FourPrimeGroupingSupport
import FourPrimeGroupingRemainder

/-! One actual four-prime divisor remainder at the exact source window.
The data below contain finite supports, elementary scale restrictions and
bounded coefficients. They contain no mean-square estimate, prime-count
conclusion, or unconstructed assertion that these coefficients arise from
a linear sieve. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace FourPrimeSourceBlock
open FourPrimeScaleBudget

structure Data (s X : ℝ) where
  S0 : Finset ℕ
  S1 : Finset ℕ
  S2 : Finset ℕ
  S3 : Finset ℕ
  S4 : Finset ℕ
  C : ℕ → ℝ
  D1 : ℝ
  D2 : ℝ
  D3 : ℝ
  D4 : ℝ
  coefficient_bound : ∀ n ∈ S0, |C n| ≤ 1
  nu_positive : ∀ n ∈ S0, 1 ≤ n
  primes1 : ∀ n ∈ S1, n.Prime
  primes2 : ∀ n ∈ S2, n.Prime
  primes3 : ∀ n ∈ S3, n.Prime
  primes4 : ∀ n ∈ S4, n.Prime
  scale_one : 1 ≤ D4
  order43 : D4 ≤ D3
  order32 : D3 ≤ D2
  order21 : D2 ≤ D1
  cubic_product : D1 * D2 * D3 * D4 ^ 3 ≤ X ^ (1 - 3 * s)
  last_scale_lower : (X ^ (1 - 3 * s)) ^ (s ^ 2) ≤ D4
  nu_upper : ∀ n ∈ S0, (n : ℝ) ≤ (X ^ (1 - 3 * s)) ^ s
  prime_upper1 : ∀ p ∈ S1, (p : ℝ) ≤ D1 ^ (1 + s ^ 7)
  prime_upper2 : ∀ p ∈ S2, (p : ℝ) ≤ D2 ^ (1 + s ^ 7)
  prime_upper3 : ∀ p ∈ S3, (p : ℝ) ≤ D3 ^ (1 + s ^ 7)
  prime_upper4 : ∀ p ∈ S4, (p : ℝ) ≤ D4 ^ (1 + s ^ 7)
  prime_lower4 : ∀ p ∈ S4, D4 ≤ (p : ℝ)

def remainder {s X : ℝ} (B : Data s X) (L R : ℝ) : ℝ :=
  ∑ ν ∈ B.S0, ∑ p1 ∈ B.S1, ∑ p2 ∈ B.S2, ∑ p3 ∈ B.S3, ∑ p4 ∈ B.S4,
    B.C ν * ((⌊R / ((ν * p1 * p2 * p3 * p4 : ℕ) : ℝ)⌋₊ : ℝ) -
      (⌊L / ((ν * p1 * p2 * p3 * p4 : ℕ) : ℝ)⌋₊ : ℝ) -
      (R - L) / ((ν * p1 * p2 * p3 * p4 : ℕ) : ℝ))

theorem left_support_two_le {s X : ℝ} (B : Data s X) :
    ∀ m ∈ FourPrimeGrouping.support B.S0 B.S1 B.S2 B.S3, 2 ≤ m :=
  FourPrimeGrouping.support_two_le B.S0 B.S1 B.S2 B.S3
    B.nu_positive (fun n hn => (B.primes1 n hn).two_le)
    (fun n hn => (B.primes2 n hn).one_lt.le)
    (fun n hn => (B.primes3 n hn).one_lt.le)

theorem last_support_two_le {s X : ℝ} (B : Data s X) :
    ∀ n ∈ B.S4, 2 ≤ n := fun n hn => (B.primes4 n hn).two_le

theorem last_support_lower {s X : ℝ} (B : Data s X) (hX : 1 ≤ X) :
    ∀ n ∈ B.S4, X ^ lowerExponent s ≤ (n:ℝ) := by
  intro n hn
  exact last_prime_lower X s B.D4 n hX B.last_scale_lower (B.prime_lower4 n hn)

theorem last_support_upper {s X : ℝ} (B : Data s X) (hX : 1 ≤ X)
    (hs : 0 < s) (hs1 : s < 1/100) :
    ∀ n ∈ B.S4, (n:ℝ) ≤ X ^ (1/6:ℝ) := by
  intro n hn
  apply (last_prime_bound X s B.D1 B.D2 B.D3 B.D4 n hX hs hs1
    (by linarith [B.scale_one]) B.order43 B.order32 B.order21 B.cubic_product
    (B.prime_upper4 n hn)).trans
  exact Real.rpow_le_rpow_of_exponent_le hX (by linarith)

theorem cross_product_bound {s X : ℝ} (B : Data s X) (hX : 1 ≤ X)
    (hs : 0 < s) (hs1 : s < 1/100) :
    ∀ m ∈ FourPrimeGrouping.support B.S0 B.S1 B.S2 B.S3,
      ∀ n ∈ B.S4, (m:ℝ)*(n:ℝ) ≤ X ^ (1-2*s) := by
  apply FourPrimeGrouping.support_cross_upper_bound B.S0 B.S1 B.S2 B.S3 B.S4
    (X ^ (1-2*s))
  intro nu hnu p1 hp1 p2 hp2 p3 hp3 p4 hp4
  exact tuple_product_bound X s B.D1 B.D2 B.D3 B.D4 nu p1 p2 p3 p4 hX hs hs1
    B.scale_one B.order43 B.order32 B.order21 B.cubic_product
    (Nat.cast_nonneg nu) (B.nu_upper nu hnu)
    (Nat.cast_nonneg p1) (Nat.cast_nonneg p2) (Nat.cast_nonneg p3) (Nat.cast_nonneg p4)
    (B.prime_upper1 p1 hp1) (B.prime_upper2 p2 hp2)
    (B.prime_upper3 p3 hp3) (B.prime_upper4 p4 hp4)

/-- Every representation of a grouped m remains in its coefficient. -/
theorem left_coefficient_bound {s X : ℝ} (B : Data s X) :
    ∀ m ∈ FourPrimeGrouping.support B.S0 B.S1 B.S2 B.S3,
      |FourPrimeGrouping.coefficient B.S0 B.S1 B.S2 B.S3 B.C m| ≤
        (m.divisors.card:ℝ)^4 := by
  intro m hm
  exact FourPrimeGrouping.coefficient_abs_le_tau_four B.S0 B.S1 B.S2 B.S3 B.C
    (fun n hn => B.nu_positive n hn)
    (fun n hn => (B.primes1 n hn).pos)
    (fun n hn => (B.primes2 n hn).pos)
    (fun n hn => (B.primes3 n hn).pos) B.coefficient_bound m

theorem last_coefficient_bound {s X : ℝ} (B : Data s X) :
    ∀ n ∈ B.S4, |FourPrimeGrouping.lastCoefficient B.S4 n| ≤ 1 := by
  intro n hn
  exact FourPrimeGrouping.lastCoefficient_abs_le_one B.S4 n

/-- This is a finite identity, with no restrictions on the real endpoints. -/
theorem grouped_remainder_eq {s X : ℝ} (B : Data s X) (L R : ℝ) :
    HarmanDivisorWindow.remainder
      (FourPrimeGrouping.fullSupport B.S0 B.S1 B.S2 B.S3 B.S4)
      (FourPrimeGrouping.fullCoefficient B.S0 B.S1 B.S2 B.S3 B.S4 B.C) L R =
      remainder B L R :=
  FourPrimeGrouping.grouped_remainder B.S0 B.S1 B.S2 B.S3 B.S4 B.C L R

#print axioms cross_product_bound
#print axioms grouped_remainder_eq
run_cmd do
  for target in [``left_support_two_le, ``last_support_two_le,
      ``last_support_lower, ``last_support_upper, ``cross_product_bound,
      ``left_coefficient_bound, ``last_coefficient_bound, ``grouped_remainder_eq] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "FOUR_PRIME_SOURCE_DATA_PASSED; SIEVE_COEFFICIENT_CONSTRUCTION_NOT_ASSERTED"

end FourPrimeSourceBlock
end
