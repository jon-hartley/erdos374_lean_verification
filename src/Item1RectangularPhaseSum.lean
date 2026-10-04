import Item1PolynomialTupleProduct

/-! Exact separation of integer-coordinate phase sums on finite rectangles.
The weighted identity supports finite approximations to product majorants.
The bounds here only combine explicitly supplied one-dimensional bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace Item1RectangularPhaseSum
open Item1PhasePerturbation Item1PolynomialTupleProduct

/-- A rectangular angular phase separates even with coordinate weights. -/
theorem weighted_rectangular_phase_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : ι → Finset ℤ) (θ : ι → ℝ) (ρ : ι → ℤ → ℂ) :
    (∑ c ∈ Fintype.piFinset I,
      (∏ j, ρ j (c j))*unitPhase (∑ j, θ j*(c j:ℝ))) =
      ∏ j, ∑ n ∈ I j, ρ j n*unitPhase (θ j*(n:ℝ)) := by
  classical
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [unitPhase_finset_sum, Finset.prod_mul_distrib]

/-- Exact rectangular factorization, including empty coordinate sets. -/
theorem rectangular_phase_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : ι → Finset ℤ) (θ : ι → ℝ) :
    (∑ c ∈ Fintype.piFinset I, unitPhase (∑ j, θ j*(c j:ℝ))) =
      ∏ j, ∑ n ∈ I j, unitPhase (θ j*(n:ℝ)) := by
  simpa only [Finset.prod_const_one, one_mul] using
    weighted_rectangular_phase_sum I θ (fun _ _ => 1)

/-- The norm factors exactly, before any arithmetic estimate is used. -/
theorem norm_rectangular_phase_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : ι → Finset ℤ) (θ : ι → ℝ) :
    ‖∑ c ∈ Fintype.piFinset I, unitPhase (∑ j, θ j*(c j:ℝ))‖ =
      ∏ j, ‖∑ n ∈ I j, unitPhase (θ j*(n:ℝ))‖ := by
  rw [rectangular_phase_sum, norm_prod]

/-- Coordinate estimates multiply without loss on the rectangle. -/
theorem norm_rectangular_phase_sum_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : ι → Finset ℤ) (θ D : ι → ℝ)
    (hD : ∀ j, ‖∑ n ∈ I j, unitPhase (θ j*(n:ℝ))‖ ≤ D j) :
    ‖∑ c ∈ Fintype.piFinset I, unitPhase (∑ j, θ j*(c j:ℝ))‖ ≤
      ∏ j, D j := by
  rw [norm_rectangular_phase_sum I θ]
  exact Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => hD j)

/-- The unconditional cardinality bound handles every degenerate rectangle. -/
theorem norm_rectangular_phase_sum_le_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : ι → Finset ℤ) (θ : ι → ℝ) :
    ‖∑ c ∈ Fintype.piFinset I, unitPhase (∑ j, θ j*(c j:ℝ))‖ ≤
      ∏ j, ((I j).card:ℝ) := by
  apply norm_rectangular_phase_sum_le
  intro j
  simpa only [unitPhase_norm, Finset.sum_const, nsmul_eq_mul, mul_one] using
    norm_sum_le (I j) (fun n => unitPhase (θ j*(n:ℝ)))

end Item1RectangularPhaseSum

run_cmd do
  for target in [``Item1RectangularPhaseSum.weighted_rectangular_phase_sum,
      ``Item1RectangularPhaseSum.rectangular_phase_sum,
      ``Item1RectangularPhaseSum.norm_rectangular_phase_sum,
      ``Item1RectangularPhaseSum.norm_rectangular_phase_sum_le,
      ``Item1RectangularPhaseSum.norm_rectangular_phase_sum_le_card] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "RECTANGULAR PHASE SUM: 5 standard-axiom theorem guards passed."
