import Item1BoxMomentMajorant
import Item1DisplacedCollisionBound

/-! The tuple-pair majorant is bounded by an exact zero-displacement
collision count times a product of one-dimensional arithmetic sums.
Repeated tuple frequencies retain their full multiplicity. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators

namespace Item1DifferenceBoxMajorant
open Item1BoxMomentMajorant Item1LinearPhaseDistance Item1PowerSumBox
open Item1KernelCorrelation Item1PolynomialMomentIdentity Item1TupleCollisionCounting
open Item1DisplacedCollisionBound

def differenceBox (d s Bmax : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun j : Fin d =>
    Finset.Icc (-((s*Bmax^(j.val+1):ℕ):ℤ)) ((s*Bmax^(j.val+1):ℕ):ℤ))

def differenceWeight (d r A : ℕ) (α : Fin d → ℝ) (δ : Fin d → ℤ) : ℝ :=
  ∏ j : Fin d, distanceBound (r*A^(j.val+1)+1) ((α j*(δ j:ℝ))/(2*Real.pi))

def arithmeticProduct (d r s A Bmax : ℕ) (α : Fin d → ℝ) : ℝ :=
  ∏ j : Fin d,
    ∑ δ ∈ Finset.Icc (-((s*Bmax^(j.val+1):ℕ):ℤ)) ((s*Bmax^(j.val+1):ℕ):ℤ),
      distanceBound (r*A^(j.val+1)+1) ((α j*(δ:ℝ))/(2*Real.pi))

def secondCollisionCount {κ : Type*} [Fintype κ] (d s : ℕ) (u : κ → ℤ) : ℝ :=
  ∑ c ∈ frequencyImage
    (tupleFrequency (r := s) (powerFrequency d u) : (Fin s → κ) → (Fin d → ℤ)),
    (fiberMultiplicity (tupleFrequency (r := s) (powerFrequency d u)) c : ℝ)^2

def pairDifference {κ : Type*} (d s : ℕ) (u : κ → ℤ)
    (pq : (Fin s → κ) × (Fin s → κ)) : Fin d → ℤ :=
  differenceFrequency d s u pq.1 pq.2

theorem differenceWeight_nonneg (d r A : ℕ) (α : Fin d → ℝ) (δ : Fin d → ℤ) :
    0 ≤ differenceWeight d r A α δ :=
  Finset.prod_nonneg (fun _j _ => distanceBound_nonneg _ _)

/-- Every tuple difference lies in the full symmetric coordinate box. -/
theorem differenceFrequency_mem_differenceBox {κ : Type*} (d s Bmax : ℕ)
    (u : κ → ℤ) (hu0 : ∀ b, 0 ≤ u b) (huB : ∀ b, u b ≤ (Bmax:ℤ))
    (p q : Fin s → κ) :
    differenceFrequency d s u p q ∈ differenceBox d s Bmax := by
  simp only [differenceBox, Fintype.mem_piFinset, Finset.mem_Icc]
  intro j
  have hp := tuple_coordinate_bounds d s Bmax u hu0 huB p j
  have hq := tuple_coordinate_bounds d s Bmax u hu0 huB q j
  simp only [differenceFrequency, Pi.sub_apply, Nat.cast_mul, Nat.cast_pow]
  constructor <;> omega

/-- The nonnegative weight separates exactly on the finite coordinate box. -/
theorem sum_differenceWeight_eq_arithmeticProduct (d r s A Bmax : ℕ)
    (α : Fin d → ℝ) :
    (∑ δ ∈ differenceBox d s Bmax, differenceWeight d r A α δ) =
      arithmeticProduct d r s A Bmax α := by
  unfold arithmeticProduct
  rw [Finset.prod_univ_sum]
  rfl

/-- A prescribed tuple difference occurs no more often than zero difference. -/
theorem pairMultiplicity_le_secondCollisionCount {κ : Type*} [Fintype κ]
    (d s : ℕ) (u : κ → ℤ) (δ : Fin d → ℤ) :
    (fiberMultiplicity (pairDifference d s u) δ : ℝ) ≤ secondCollisionCount d s u := by
  classical
  have h := displaced_collision_le_zero
    (tupleFrequency (r := s) (powerFrequency d u) : (Fin s → κ) → (Fin d → ℤ)) δ
  rw [collisions_eq_sum_multiplicity_sq] at h
  have hcount : (fiberMultiplicity (pairDifference d s u) δ : ℝ) =
      ∑ pq : (Fin s → κ) × (Fin s → κ),
        if pairDifference d s u pq = δ then (1:ℝ) else 0 := by
    simp only [fiberMultiplicity, Finset.sum_boole]
  rw [hcount, Fintype.sum_prod_type]
  dsimp only [pairDifference, differenceFrequency, secondCollisionCount]
  convert h using 1 <;> first | rfl |
    (apply Finset.sum_congr rfl
     intro p _
     apply Finset.sum_congr rfl
     intro q _
     split <;> split <;> simp_all)

/-- The pair-frequency sum is bounded by the zero-displacement collision
factor and independent one-dimensional arithmetic sums. -/
theorem momentMajorant_le_collision_arithmeticProduct {κ : Type*} [Fintype κ]
    (d r s A Bmax : ℕ) (α : Fin d → ℝ) (u : κ → ℤ)
    (hu0 : ∀ b, 0 ≤ u b) (huB : ∀ b, u b ≤ (Bmax:ℤ)) :
    momentMajorant d r s A α u ≤
      secondCollisionCount d s u * arithmeticProduct d r s A Bmax α := by
  classical
  let f := pairDifference d s u
  have hsubset : frequencyImage f ⊆ differenceBox d s Bmax := by
    intro δ hδ
    obtain ⟨pq, hpq, rfl⟩ := Finset.mem_image.mp hδ
    exact differenceFrequency_mem_differenceBox d s Bmax u hu0 huB pq.1 pq.2
  have hgroup : momentMajorant d r s A α u =
      ∑ δ ∈ frequencyImage f, (fiberMultiplicity f δ:ℝ)*differenceWeight d r A α δ := by
    rw [← sum_grouped f (differenceWeight d r A α)]
    simp only [Fintype.sum_prod_type, momentMajorant, pairBound,
      f, pairDifference, differenceWeight]
  have hJ : 0 ≤ secondCollisionCount d s u := by
    unfold secondCollisionCount
    positivity
  calc
    momentMajorant d r s A α u =
        ∑ δ ∈ frequencyImage f, (fiberMultiplicity f δ:ℝ)*differenceWeight d r A α δ := hgroup
    _ ≤ ∑ δ ∈ frequencyImage f, secondCollisionCount d s u*differenceWeight d r A α δ := by
      apply Finset.sum_le_sum
      intro δ hδ
      exact mul_le_mul_of_nonneg_right (pairMultiplicity_le_secondCollisionCount d s u δ)
        (differenceWeight_nonneg d r A α δ)
    _ = secondCollisionCount d s u *
        (∑ δ ∈ frequencyImage f, differenceWeight d r A α δ) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ secondCollisionCount d s u *
        (∑ δ ∈ differenceBox d s Bmax, differenceWeight d r A α δ) := by
      apply mul_le_mul_of_nonneg_left _ hJ
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun δ _ _ => differenceWeight_nonneg d r A α δ)
    _ = secondCollisionCount d s u * arithmeticProduct d r s A Bmax α := by
      rw [sum_differenceWeight_eq_arithmeticProduct]

end Item1DifferenceBoxMajorant

run_cmd do
  for target in [``Item1DifferenceBoxMajorant.differenceWeight_nonneg,
      ``Item1DifferenceBoxMajorant.differenceFrequency_mem_differenceBox,
      ``Item1DifferenceBoxMajorant.sum_differenceWeight_eq_arithmeticProduct,
      ``Item1DifferenceBoxMajorant.pairMultiplicity_le_secondCollisionCount,
      ``Item1DifferenceBoxMajorant.momentMajorant_le_collision_arithmeticProduct] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "DIFFERENCE BOX MAJORANT: 5 standard-axiom theorem guards passed."
