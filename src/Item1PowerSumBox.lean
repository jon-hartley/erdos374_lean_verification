import Item1TupleCollisionCounting
import Item1PolynomialTupleProduct
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators

/-! An explicit integer box containing the power-sum frequencies of bounded
nonnegative integer inputs. Sums with nonnegative summands may be enlarged
from the attained frequencies to the whole box. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace Item1PowerSumBox
open Item1PolynomialMomentIdentity Item1TupleCollisionCounting

/-- Coordinate `j` ranges over the integers from zero through `r*A^(j+1)`.
The finite box retains its natural meaning when any parameter is zero. -/
def box (d r A : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun j : Fin d => Finset.Icc 0 ((r * A ^ (j.val + 1) : ℕ) : ℤ))

theorem mem_box_iff (d r A : ℕ) (c : Fin d → ℤ) :
    c ∈ box d r A ↔
      ∀ j : Fin d, 0 ≤ c j ∧ c j ≤ (r : ℤ) * (A : ℤ) ^ (j.val + 1) := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc, Nat.cast_mul, Nat.cast_pow]

/-- The cardinality is exact, including the zero-dimensional singleton box. -/
theorem card_box (d r A : ℕ) :
    (box d r A).card = ∏ j : Fin d, (r * A ^ (j.val + 1) + 1) := by
  rw [box, Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Int.card_Icc, sub_zero]
  norm_cast

theorem tuple_coordinate_bounds {ι : Type*} (d r A : ℕ) (w : ι → ℤ)
    (hw0 : ∀ i, 0 ≤ w i) (hwA : ∀ i, w i ≤ (A : ℤ))
    (p : Fin r → ι) (j : Fin d) :
    0 ≤ tupleFrequency (powerFrequency d w) p j ∧
      tupleFrequency (powerFrequency d w) p j ≤
        (r : ℤ) * (A : ℤ) ^ (j.val + 1) := by
  simp only [tupleFrequency, Finset.sum_apply, powerFrequency]
  constructor
  · exact Finset.sum_nonneg (fun l _ => pow_nonneg (hw0 (p l)) _)
  · calc
      (∑ l : Fin r, w (p l) ^ (j.val + 1)) ≤
          ∑ _l : Fin r, (A : ℤ) ^ (j.val + 1) :=
        Finset.sum_le_sum (fun l _ => pow_le_pow_left₀ (hw0 (p l)) (hwA (p l)) _)
      _ = (r : ℤ) * (A : ℤ) ^ (j.val + 1) := by simp

theorem tupleFrequency_mem_box {ι : Type*} (d r A : ℕ) (w : ι → ℤ)
    (hw0 : ∀ i, 0 ≤ w i) (hwA : ∀ i, w i ≤ (A : ℤ))
    (p : Fin r → ι) :
    tupleFrequency (powerFrequency d w) p ∈ box d r A := by
  rw [mem_box_iff]
  exact tuple_coordinate_bounds d r A w hw0 hwA p

theorem frequencyImage_subset_box {ι : Type*} [Fintype ι]
    (d r A : ℕ) (w : ι → ℤ)
    (hw0 : ∀ i, 0 ≤ w i) (hwA : ∀ i, w i ≤ (A : ℤ)) :
    frequencyImage
      (tupleFrequency (r := r) (powerFrequency d w) : (Fin r → ι) → (Fin d → ℤ)) ⊆
        box d r A := by
  classical
  intro c hc
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
  exact tupleFrequency_mem_box d r A w hw0 hwA p

/-- Only summands in the box need to be nonnegative. -/
theorem sum_frequencyImage_le_box {ι : Type*} [Fintype ι]
    (d r A : ℕ) (w : ι → ℤ)
    (hw0 : ∀ i, 0 ≤ w i) (hwA : ∀ i, w i ≤ (A : ℤ))
    (F : (Fin d → ℤ) → ℝ) (hF : ∀ c ∈ box d r A, 0 ≤ F c) :
    (∑ c ∈ frequencyImage
      (tupleFrequency (r := r) (powerFrequency d w) : (Fin r → ι) → (Fin d → ℤ)), F c) ≤
        ∑ c ∈ box d r A, F c := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (frequencyImage_subset_box d r A w hw0 hwA) (fun c hc _ => hF c hc)

theorem sum_norm_pow_frequencyImage_le_box {ι : Type*} [Fintype ι]
    (d r A : ℕ) (w : ι → ℤ)
    (hw0 : ∀ i, 0 ≤ w i) (hwA : ∀ i, w i ≤ (A : ℤ))
    (F : (Fin d → ℤ) → ℂ) (q : ℕ) :
    (∑ c ∈ frequencyImage
      (tupleFrequency (r := r) (powerFrequency d w) : (Fin r → ι) → (Fin d → ℤ)), ‖F c‖ ^ q) ≤
        ∑ c ∈ box d r A, ‖F c‖ ^ q := by
  exact sum_frequencyImage_le_box d r A w hw0 hwA (fun c => ‖F c‖ ^ q)
    (fun c _ => pow_nonneg (norm_nonneg (F c)) q)

/-- The weighted kernel moment in the bilinear reduction may be summed over
the whole explicit box. No unit-norm condition on the weights is needed. -/
theorem kernel_moment_sum_le_box {ι κ : Type*} [Fintype ι] [Fintype κ]
    (d r s A : ℕ) (α : Fin d → ℝ) (w : ι → ℤ) (u : κ → ℤ) (ε : κ → ℂ)
    (hw0 : ∀ i, 0 ≤ w i) (hwA : ∀ i, w i ≤ (A : ℤ)) :
    (∑ c ∈ frequencyImage
      (tupleFrequency (r := r) (powerFrequency d w) : (Fin r → ι) → (Fin d → ℤ)),
        ‖∑ b, ε b * Item1PolynomialTupleProduct.kernel α u c b‖ ^ (2 * s)) ≤
      ∑ c ∈ box d r A,
        ‖∑ b, ε b * Item1PolynomialTupleProduct.kernel α u c b‖ ^ (2 * s) := by
  exact sum_norm_pow_frequencyImage_le_box d r A w hw0 hwA
    (fun c => ∑ b, ε b * Item1PolynomialTupleProduct.kernel α u c b) (2 * s)

end Item1PowerSumBox

run_cmd do
  for target in [``Item1PowerSumBox.mem_box_iff,
      ``Item1PowerSumBox.card_box,
      ``Item1PowerSumBox.tuple_coordinate_bounds,
      ``Item1PowerSumBox.tupleFrequency_mem_box,
      ``Item1PowerSumBox.frequencyImage_subset_box,
      ``Item1PowerSumBox.sum_frequencyImage_le_box,
      ``Item1PowerSumBox.sum_norm_pow_frequencyImage_le_box,
      ``Item1PowerSumBox.kernel_moment_sum_le_box] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "POWER SUM BOX: 8 standard-axiom theorem guards passed."
