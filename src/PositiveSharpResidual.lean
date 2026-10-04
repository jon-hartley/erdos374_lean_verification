import PositiveSharpCounts

/-! Exact normalization of the literal sharp-window counts against the
already checked dyadic Mangoldt model. The residual is retained explicitly;
this module supplies no pointwise or mean estimate for its size. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators
namespace PositiveSharpResidual
open PositiveSharpCounts PositiveInteriorModel PositiveInteriorCells

def cellResidual (X : ℝ) (j : ℕ × ℕ) (x y : ℝ) : ℝ :=
  (weightedCount X j x y-y*reciprocalMass (scale j.1)*reciprocalMass (scale j.2))/
    (y*denominator X j)
def deletionCell (X : ℝ) (j : ℕ × ℕ) (x y : ℝ) : ℝ :=
  deletionCount X j x y/(y*denominator X j)
def totalResidual (X x y : ℝ) : ℝ := ∑ j ∈ boxes (mesh X), cellResidual X j x y
def residualAbs (X x y : ℝ) : ℝ := ∑ j ∈ boxes (mesh X), |cellResidual X j x y|
def deletionTotal (X x y : ℝ) : ℝ := ∑ j ∈ boxes (mesh X), deletionCell X j x y
def primeContribution (X x y : ℝ) : ℝ :=
  ∑ j ∈ boxes (mesh X),
    (weightedCount X j x y-deletionCount X j x y)/(y*denominator X j)
def orderedCount (X x y : ℝ) : ℕ := ∑ j ∈ boxes (mesh X), primeCount X j x y

theorem cell_identity (X x y : ℝ) (hy : y≠0) (j : ℕ × ℕ)
    (hd : denominator X j≠0) :
    (weightedCount X j x y-deletionCount X j x y)/(y*denominator X j)=
      cellModel X j+cellResidual X j x y-deletionCell X j x y := by
  unfold cellModel cellResidual deletionCell
  field_simp
  ring

theorem aggregate_identity (X x y : ℝ) (hX : 1<X) (hs : mesh X≤1/1000000)
    (hy : 0<y) :
    primeContribution X x y=model X+totalResidual X x y-deletionTotal X x y := by
  unfold primeContribution model totalResidual deletionTotal
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  exact cell_identity X x y hy.ne' j (denominator_bounds X hX hs j hj).1.ne'

theorem residualAbs_nonneg (X x y : ℝ) : 0≤residualAbs X x y :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem totalResidual_abs_le (X x y : ℝ) :
    |totalResidual X x y|≤residualAbs X x y := Finset.abs_sum_le_sum_abs _ _

theorem deletionTotal_nonneg (X x y : ℝ) (hX : 1<X) (hs : mesh X≤1/1000000)
    (hy : 0<y) : 0≤deletionTotal X x y := by
  apply Finset.sum_nonneg
  intro j hj
  exact div_nonneg (deletionCount_nonneg X x y j)
    (mul_pos hy (denominator_bounds X hX hs j hj).1).le

theorem model_sub_errors_le (X x y : ℝ) (hX : 1<X) (hs : mesh X≤1/1000000)
    (hy : 0<y) :
    model X-residualAbs X x y-deletionTotal X x y≤primeContribution X x y := by
  rw [aggregate_identity X x y hX hs hy]
  have hh := (abs_le.mp (totalResidual_abs_le X x y)).1
  linarith

theorem primeContribution_nonneg (X x y : ℝ) (hX : 1<X) (hs : mesh X≤1/1000000)
    (hy : 0<y) : 0≤primeContribution X x y := by
  apply Finset.sum_nonneg
  intro j hj
  rw [exact_prime_coordinate_deletion]
  exact div_nonneg (primeWeightedCount_nonneg X x y j)
    (mul_pos hy (denominator_bounds X hX hs j hj).1).le

theorem primeContribution_le_orderedCount (X x y : ℝ) (hX : 1<X)
    (hs : mesh X≤1/1000000) (hy : 0<y) :
    primeContribution X x y≤(orderedCount X x y:ℝ)/y := by
  unfold primeContribution orderedCount
  rw [Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hh := div_le_div_of_nonneg_right (prime_count_minorant X x y hX hs j hj).2 hy.le
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using hh

theorem orderedCount_lower (X x y : ℝ) (hX : 1<X)
    (hs : mesh X≤1/1000000) (hy : 0<y) :
    model X-residualAbs X x y-deletionTotal X x y≤(orderedCount X x y:ℝ)/y :=
  (model_sub_errors_le X x y hX hs hy).trans
    (primeContribution_le_orderedCount X x y hX hs hy)

run_cmd do
  for decl in [``cell_identity, ``aggregate_identity, ``residualAbs_nonneg,
      ``totalResidual_abs_le, ``deletionTotal_nonneg, ``model_sub_errors_le,
      ``primeContribution_nonneg, ``primeContribution_le_orderedCount, ``orderedCount_lower] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXACT ACTUAL COUNT/MODEL/RESIDUAL IDENTITY; RESIDUAL SMALLNESS UNPROVED"
end PositiveSharpResidual
end
