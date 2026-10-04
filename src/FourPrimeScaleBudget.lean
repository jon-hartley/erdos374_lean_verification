import PolynomialLogEnvelope
import DivisorPowerBound

/-! Scalar budgets for the proposed four-prime block. These statements
do not construct sieve coefficients or assert a positive prime count. -/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter

namespace FourPrimeScaleBudget

def lowerExponent (s : ℝ) : ℝ := (1 - 3 * s) * s ^ 2

theorem lowerExponent_pos (s : ℝ) (hs : 0 < s) (hs1 : s < 1 / 100) :
    0 < lowerExponent s := by
  unfold lowerExponent
  exact mul_pos (by linarith) (sq_pos_of_pos hs)

theorem exponent_margins (s : ℝ) (hs : 0 < s) (hs1 : s < 1 / 100) :
    (1 - 3 * s) * (1 + s ^ 7) ≤ 1 - 2 * s ∧
      (1 - 3 * s) * (1 + s + s ^ 7) ≤ 1 - 2 * s ∧
      (1 - 2 * s) / 6 ≤ 8 / 35 := by
  have hsone : s ≤ 1 := by linarith
  have h7s : s ^ 7 ≤ s := by
    calc
      s ^ 7 = s * s ^ 6 := by ring
      _ ≤ s * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hs.le hsone) hs.le
      _ = s := mul_one s
  have h7sq : s ^ 7 ≤ s ^ 2 := by
    calc
      s ^ 7 = s ^ 2 * s ^ 5 := by ring
      _ ≤ s ^ 2 * 1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ hs.le hsone) (sq_nonneg s)
      _ = s ^ 2 := mul_one _
  have h8 : 0 ≤ s * s ^ 7 := mul_nonneg hs.le (pow_nonneg hs.le _)
  constructor
  · nlinarith
  constructor
  · nlinarith [sq_nonneg s]
  · linarith

theorem last_scale_sixth_power (D1 D2 D3 D4 D : ℝ)
    (h4 : 0 ≤ D4) (h43 : D4 ≤ D3) (h32 : D3 ≤ D2) (h21 : D2 ≤ D1)
    (hproduct : D1 * D2 * D3 * D4 ^ 3 ≤ D) : D4 ^ 6 ≤ D := by
  have h3 : 0 ≤ D3 := h4.trans h43
  have h2 : 0 ≤ D2 := h3.trans h32
  have h1 : 0 ≤ D1 := h2.trans h21
  calc
    D4 ^ 6 = D4 * D4 * D4 * D4 ^ 3 := by ring
    _ ≤ D1 * D2 * D3 * D4 ^ 3 := by gcongr <;> linarith
    _ ≤ D := hproduct

theorem last_scale_bound (X s D1 D2 D3 D4 : ℝ)
    (hX : 1 ≤ X) (h4 : 0 ≤ D4)
    (h43 : D4 ≤ D3) (h32 : D3 ≤ D2) (h21 : D2 ≤ D1)
    (hproduct : D1 * D2 * D3 * D4 ^ 3 ≤ X ^ (1 - 3 * s)) :
    D4 ≤ X ^ ((1 - 3 * s) / 6) := by
  have hh := last_scale_sixth_power D1 D2 D3 D4 (X ^ (1 - 3 * s))
    h4 h43 h32 h21 hproduct
  have hroot := Real.rpow_le_rpow (pow_nonneg h4 6) hh
    (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hleft : (D4 ^ (6 : ℕ)) ^ (1 / 6 : ℝ) = D4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h4]
    norm_num
  rw [hleft, ← Real.rpow_mul (by linarith : 0 ≤ X)] at hroot
  convert hroot using 1
  ring

theorem last_prime_bound (X s D1 D2 D3 D4 p : ℝ)
    (hX : 1 ≤ X) (hs : 0 < s) (hs1 : s < 1 / 100)
    (h4 : 0 ≤ D4) (h43 : D4 ≤ D3) (h32 : D3 ≤ D2) (h21 : D2 ≤ D1)
    (hproduct : D1 * D2 * D3 * D4 ^ 3 ≤ X ^ (1 - 3 * s))
    (hp : p ≤ D4 ^ (1 + s ^ 7)) :
    p ≤ X ^ ((1 - 2 * s) / 6) := by
  have hD := last_scale_bound X s D1 D2 D3 D4 hX h4 h43 h32 h21 hproduct
  have hh := Real.rpow_le_rpow h4 hD
    (by positivity : 0 ≤ 1 + s ^ 7)
  rw [← Real.rpow_mul (by linarith : 0 ≤ X)] at hh
  apply (hp.trans hh).trans
  exact Real.rpow_le_rpow_of_exponent_le hX (by
    have := (exponent_margins s hs hs1).1
    nlinarith)

theorem eventually_divisor_fourth (c : ℝ) (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      ∀ m : ℕ, (m : ℝ) ≤ X → (m.divisors.card : ℝ) ^ 4 ≤ X ^ (c / 2) := by
  obtain ⟨K, hK, hcount⟩ := DivisorPowerBound.divisor_count_bound
    (c / 16) (by positivity)
  filter_upwards [PolynomialLogEnvelope.eventually_constant_bound
    (K ^ 4) (c / 4) (by positivity) (by positivity)] with X hX
  refine ⟨hX.1, ?_⟩
  intro m hm
  have hXp : 0 < X := by linarith [hX.1]
  calc
    (m.divisors.card : ℝ) ^ 4 ≤ (K * (m : ℝ) ^ (c / 16)) ^ 4 := by
      gcongr
      exact hcount m
    _ = K ^ 4 * (m : ℝ) ^ (c / 4) := by
      rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg m)]
      congr 2
      norm_num
      ring
    _ ≤ X ^ (c / 4) * X ^ (c / 4) := by
      apply mul_le_mul hX.2
        (Real.rpow_le_rpow (Nat.cast_nonneg m) hm (by positivity))
        (by positivity) (by positivity)
    _ = X ^ (c / 2) := by rw [← Real.rpow_add hXp]; congr 1; ring

theorem eventual_lower_bin_budget (s : ℝ) (hs : 0 < s) (hs1 : s < 1 / 100) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      X ^ (lowerExponent s / 2) ≤ X ^ lowerExponent s / 2 := by
  have hb := lowerExponent_pos s hs hs1
  filter_upwards [PolynomialLogEnvelope.eventually_constant_bound
    2 (lowerExponent s / 2) (by norm_num) (by positivity)] with X hh
  refine ⟨hh.1, ?_⟩
  have hXp : 0 < X := by linarith [hh.1]
  have hpow : X ^ lowerExponent s =
      X ^ (lowerExponent s / 2) * X ^ (lowerExponent s / 2) := by
    rw [← Real.rpow_add hXp]; congr 1; ring
  rw [hpow]
  nlinarith [Real.rpow_nonneg hXp.le (lowerExponent s / 2)]

end FourPrimeScaleBudget

run_cmd do
  for target in [``FourPrimeScaleBudget.lowerExponent_pos,
      ``FourPrimeScaleBudget.exponent_margins,
      ``FourPrimeScaleBudget.last_scale_sixth_power,
      ``FourPrimeScaleBudget.last_scale_bound,
      ``FourPrimeScaleBudget.last_prime_bound,
      ``FourPrimeScaleBudget.eventually_divisor_fourth,
      ``FourPrimeScaleBudget.eventual_lower_bin_budget] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "FOUR PRIME SCALE BUDGET PASSED"
