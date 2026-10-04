import FourPrimeScaleBudget

/-! Exact conversion from the proposed source D-constraints to actual
tuple-product inequalities. These are analytic input budgets, not a
construction of a linear sieve. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace FourPrimeScaleBudget

theorem ordinary_product_le_cubic (D1 D2 D3 D4 : ℝ)
    (h4 : 1 ≤ D4) (h43 : D4 ≤ D3) (h32 : D3 ≤ D2) (h21 : D2 ≤ D1) :
    D1 * D2 * D3 * D4 ≤ D1 * D2 * D3 * D4 ^ 3 := by
  have h3 : 0 ≤ D3 := le_trans (by linarith) h43
  have h2 : 0 ≤ D2 := h3.trans h32
  have h1 : 0 ≤ D1 := h2.trans h21
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  nlinarith [sq_nonneg (D4 - 1)]

theorem tuple_product_bound (X s D1 D2 D3 D4 nu p1 p2 p3 p4 : ℝ)
    (hX : 1 ≤ X) (hs : 0 < s) (hs1 : s < 1 / 100)
    (h4 : 1 ≤ D4) (h43 : D4 ≤ D3) (h32 : D3 ≤ D2) (h21 : D2 ≤ D1)
    (hproduct : D1 * D2 * D3 * D4 ^ 3 ≤ X ^ (1 - 3 * s))
    (_hnu : 0 ≤ nu) (hnub : nu ≤ (X ^ (1 - 3 * s)) ^ s)
    (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2) (hp3 : 0 ≤ p3) (hp4 : 0 ≤ p4)
    (hp1b : p1 ≤ D1 ^ (1 + s ^ 7)) (hp2b : p2 ≤ D2 ^ (1 + s ^ 7))
    (hp3b : p3 ≤ D3 ^ (1 + s ^ 7)) (hp4b : p4 ≤ D4 ^ (1 + s ^ 7)) :
    nu * p1 * p2 * p3 * p4 ≤ X ^ (1 - 2 * s) := by
  have hXp : 0 < X := by linarith
  have hD4 : 0 ≤ D4 := by linarith
  have hD3 : 0 ≤ D3 := hD4.trans h43
  have hD2 : 0 ≤ D2 := hD3.trans h32
  have hD1 : 0 ≤ D1 := hD2.trans h21
  have hD : D1 * D2 * D3 * D4 ≤ X ^ (1 - 3 * s) :=
    (ordinary_product_le_cubic D1 D2 D3 D4 h4 h43 h32 h21).trans hproduct
  have hpower : (D1 * D2 * D3 * D4) ^ (1 + s ^ 7) ≤
      (X ^ (1 - 3 * s)) ^ (1 + s ^ 7) :=
    Real.rpow_le_rpow (by positivity) hD (by positivity)
  have hP : p1 * p2 * p3 * p4 ≤ (D1 * D2 * D3 * D4) ^ (1 + s ^ 7) := by
    rw [Real.mul_rpow (by positivity) hD4, Real.mul_rpow (by positivity) hD3,
      Real.mul_rpow hD1 hD2]
    gcongr
  calc
    nu * p1 * p2 * p3 * p4 = nu * (p1 * p2 * p3 * p4) := by ring
    _ ≤ (X ^ (1 - 3 * s)) ^ s * (X ^ (1 - 3 * s)) ^ (1 + s ^ 7) :=
      mul_le_mul hnub (hP.trans hpower) (by positivity) (by positivity)
    _ = X ^ ((1 - 3 * s) * (1 + s + s ^ 7)) := by
      rw [← Real.rpow_mul hXp.le, ← Real.rpow_mul hXp.le, ← Real.rpow_add hXp]
      congr 1
      ring
    _ ≤ X ^ (1 - 2 * s) := Real.rpow_le_rpow_of_exponent_le hX
      (exponent_margins s hs hs1).2.1

theorem last_prime_lower (X s D4 p4 : ℝ) (hX : 1 ≤ X)
    (hD4 : (X ^ (1 - 3 * s)) ^ (s ^ 2) ≤ D4) (hp4 : D4 ≤ p4) :
    X ^ lowerExponent s ≤ p4 := by
  have hh := hD4.trans hp4
  rw [← Real.rpow_mul (by linarith : 0 ≤ X)] at hh
  exact hh

end FourPrimeScaleBudget

run_cmd do
  for target in [``FourPrimeScaleBudget.ordinary_product_le_cubic,
      ``FourPrimeScaleBudget.tuple_product_bound,
      ``FourPrimeScaleBudget.last_prime_lower] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "FOUR PRIME SOURCE SCALES PASSED"
