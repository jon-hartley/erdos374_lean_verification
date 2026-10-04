import Item1PolynomialMomentIdentity

/-! Finite frequency multiplicities and the exact moment count grouped by
frequency. No estimate on these multiplicities is assumed or proved here. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory UnitAddTorus

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace Item1TupleCollisionCounting

def frequencyImage {ι η : Type*} [Fintype ι] [DecidableEq η]
    (f : ι → η) : Finset η := Finset.univ.image f

def fiberMultiplicity {ι η : Type*} [Fintype ι] [DecidableEq η]
    (f : ι → η) (c : η) : ℕ := (Finset.univ.filter (fun i => f i = c)).card

/-- Regroup a sum by its frequency, retaining every repeated occurrence. -/
theorem sum_grouped {ι η R : Type*} [Fintype ι] [DecidableEq η] [Semiring R]
    (f : ι → η) (F : η → R) :
    (∑ i, F (f i)) =
      ∑ c ∈ frequencyImage f, (fiberMultiplicity f c : R)*F c := by
  simpa only [frequencyImage, fiberMultiplicity, nsmul_eq_mul] using
    (Finset.sum_comp (s := Finset.univ) F f)

/-- Total multiplicity is exactly the number of original indices. -/
theorem sum_multiplicity {ι η : Type*} [Fintype ι] [DecidableEq η]
    (f : ι → η) :
    (∑ c ∈ frequencyImage f, fiberMultiplicity f c) = Fintype.card ι := by
  simpa only [frequencyImage, fiberMultiplicity, Finset.card_univ] using
    (Finset.card_eq_sum_card_image f Finset.univ).symm

/-- Ordered frequency collisions are exactly the sum of squared multiplicities. -/
theorem collisions_eq_sum_multiplicity_sq {ι η : Type*}
    [Fintype ι] [DecidableEq η] (f : ι → η) :
    (∑ i, ∑ j, if f i = f j then (1 : ℝ) else 0) =
      ∑ c ∈ frequencyImage f, (fiberMultiplicity f c : ℝ)^2 := by
  have hrow (i : ι) : (∑ j, if f i = f j then (1 : ℝ) else 0) =
      (fiberMultiplicity f (f i) : ℝ) := by
    simp only [fiberMultiplicity, eq_comm, Finset.sum_boole]
  simp_rw [hrow]
  rw [sum_grouped f (fun c => (fiberMultiplicity f c : ℝ))]
  simp only [pow_two]

/-- The exact polynomial moment is the squared-multiplicity count used in
finite mean-value arguments. This is still an identity, without an upper bound. -/
theorem polynomial_moment_eq_sum_multiplicity_sq {ι : Type*} [Fintype ι]
    (d r : ℕ) (w : ι → ℤ) :
    (∫ a : UnitAddTorus (Fin d),
      ‖∑ i, mFourier (Item1PolynomialMomentIdentity.powerFrequency d w i) a‖^(2*r)) =
      ∑ c ∈ frequencyImage
          (Item1PolynomialMomentIdentity.tupleFrequency (r := r)
            (Item1PolynomialMomentIdentity.powerFrequency d w) : (Fin r → ι) → (Fin d → ℤ)),
        (fiberMultiplicity
          (Item1PolynomialMomentIdentity.tupleFrequency (r := r)
            (Item1PolynomialMomentIdentity.powerFrequency d w)) c : ℝ)^2 := by
  classical
  rw [Item1PolynomialMomentIdentity.even_moment_eq_collisions]
  exact collisions_eq_sum_multiplicity_sq _

end Item1TupleCollisionCounting

run_cmd do
  for target in [``Item1TupleCollisionCounting.sum_grouped,
      ``Item1TupleCollisionCounting.sum_multiplicity,
      ``Item1TupleCollisionCounting.collisions_eq_sum_multiplicity_sq,
      ``Item1TupleCollisionCounting.polynomial_moment_eq_sum_multiplicity_sq] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "TUPLE COLLISION COUNTING: 4 standard-axiom theorem guards passed."
