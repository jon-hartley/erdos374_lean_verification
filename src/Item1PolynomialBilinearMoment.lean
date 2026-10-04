import Item1BilinearMomentReduction
import Item1PolynomialTupleProduct
import Item1PolynomialFourierBridge

/-! The finite moment reduction specialized to genuine polynomial phases,
including the actual coefficients produced by logarithmic Taylor expansion.
No upper bound on the collision count or final moment sum is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section

namespace Item1PolynomialBilinearMoment
open Item1TupleCollisionCounting Item1PolynomialMomentIdentity
open Item1PolynomialTupleProduct Item1BilinearMomentReduction
open Item1LogPhasePolynomialReduction

/-- The polynomial tuple factorization discharges the algebraic premise of
the general bilinear reduction. Integer inputs may be repeated or negative. -/
theorem polynomial_bilinear_even_moment_reduction {ι κ : Type*}
    [Fintype ι] [Fintype κ] (d r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (α : Fin d → ℝ) (w : ι → ℤ) (u : κ → ℤ) :
    let f : (Fin r → ι) → (Fin d → ℤ) := tupleFrequency (powerFrequency d w)
    ∃ ε : κ → ℂ, (∀ b, ‖ε b‖ = 1) ∧
      ‖∑ b, ∑ i, bilinearPhase α w u i b‖^(2*r*s) ≤
        (Fintype.card κ : ℝ)^(2*r*s-2*s) *
        (Fintype.card ι : ℝ)^(2*r*s-2*r) *
        (∑ c ∈ frequencyImage f, (fiberMultiplicity f c : ℝ)^2) *
        (∑ c ∈ frequencyImage f, ‖∑ b, ε b*kernel α u c b‖^(2*s)) := by
  classical
  exact bilinear_even_moment_reduction r s hr hs (bilinearPhase α w u)
    (tupleFrequency (powerFrequency d w)) (kernel α u)
    (tuple_product_eq_kernel α w u)

/-- Exact identification of the bilinear phase at the logarithmic Taylor coefficients. -/
theorem bilinearPhase_taylor_eq {ι κ : Type*} (d : ℕ) (x t : ℝ)
    (w : ι → ℤ) (u : κ → ℤ) (i : ι) (b : κ) :
    bilinearPhase (fun j : Fin d => phaseCoefficient x t j.val) w u i b =
      polynomialPhase d x t ((w i*u b : ℤ) : ℝ) := by
  unfold bilinearPhase
  rw [polynomialPhase_eq, ← Fin.sum_univ_eq_sum_range
    (fun k : ℕ => phaseCoefficient x t k * (((w i*u b : ℤ) : ℝ)^(k+1)))]

/-- The full finite moment reduction for the exact Taylor polynomials.
This does not yet estimate either the collision factor or the remaining sum. -/
theorem taylor_bilinear_even_moment_reduction {ι κ : Type*}
    [Fintype ι] [Fintype κ] (d r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (x t : ℝ) (w : ι → ℤ) (u : κ → ℤ) :
    let f : (Fin r → ι) → (Fin d → ℤ) := tupleFrequency (powerFrequency d w)
    ∃ ε : κ → ℂ, (∀ b, ‖ε b‖ = 1) ∧
      ‖∑ b, ∑ i, polynomialPhase d x t ((w i*u b : ℤ) : ℝ)‖^(2*r*s) ≤
        (Fintype.card κ : ℝ)^(2*r*s-2*s) *
        (Fintype.card ι : ℝ)^(2*r*s-2*r) *
        (∑ c ∈ frequencyImage f, (fiberMultiplicity f c : ℝ)^2) *
        (∑ c ∈ frequencyImage f,
          ‖∑ b, ε b*kernel (fun j : Fin d => phaseCoefficient x t j.val) u c b‖^(2*s)) := by
  simpa only [bilinearPhase_taylor_eq] using
    polynomial_bilinear_even_moment_reduction d r s hr hs
      (fun j : Fin d => phaseCoefficient x t j.val) w u

end Item1PolynomialBilinearMoment

run_cmd do
  for target in [``Item1PolynomialBilinearMoment.polynomial_bilinear_even_moment_reduction,
      ``Item1PolynomialBilinearMoment.bilinearPhase_taylor_eq,
      ``Item1PolynomialBilinearMoment.taylor_bilinear_even_moment_reduction] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "POLYNOMIAL BILINEAR MOMENT: 3 standard-axiom theorem guards passed."
