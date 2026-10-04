import LongerTupleMaskedCollection
import LongerTupleDyadic

/-! Select rectangles using the original masks before Fourier expansion.
Individual Fourier modes need not vanish on an inactive rectangle. The
joint partition is therefore applied to the complete original summand. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LongerTupleJointExpansion
open LongerTupleCollection LongerTupleMaskedCollection ShortSingletonMasks
open ShortSingletonComplex FourPrimePartition
open UpperAfter545Remaining (floorKernel)

variable {α : Type*}

def maskedCoefficient (S : Finset α) (index : α → ℕ) (w : α → ℂ)
    (lo hi : α → ℕ) (cut : ℕ → ℕ) (m q : ℕ) : ℂ :=
  coefficient S index (fun a => w a *
    ((prefixIndicator (hi a) q - prefixIndicator (lo a) q) *
      (1-prefixIndicator (cut (index a)) q))) m

theorem coefficient_expansion (S : Finset α) (index : α → ℕ)
    (Q : ℕ) (w : α → ℂ) (lo hi : α → ℕ) (cut : ℕ → ℕ)
    (m q : ℕ) (hq : q ≤ Q) :
    maskedCoefficient S index w lo hi cut m q =
      ∑ t : Mode Q, scalar Q t *
        modeCoefficient S index Q t w lo hi cut m * rightPhase Q t q := by
  unfold maskedCoefficient modeCoefficient coefficient
  calc
    _ = ∑ a ∈ S.filter (fun a => index a = m),
        ∑ t : Mode Q, scalar Q t * modeWeight index Q t w lo hi cut a * rightPhase Q t q := by
      apply Finset.sum_congr rfl
      intro a _
      dsimp only
      rw [separation Q _ _ _ q hq, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      unfold modeWeight
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.mul_sum, Finset.sum_mul]

theorem maskedSum_collected (S : Finset α) (index : α → ℕ) (B : Finset ℕ)
    (w : α → ℂ) (lo hi : α → ℕ) (cut : ℕ → ℕ) (L R : ℝ) :
    maskedSum S index B w lo hi cut L R =
      ∑ m ∈ support S index, ∑ q ∈ B,
        maskedCoefficient S index w lo hi cut m q * (floorKernel L R (m*q):ℂ) := by
  unfold maskedSum
  rw [Finset.sum_comm, Finset.sum_comm (s := support S index)]
  apply Finset.sum_congr rfl
  intro q _
  exact (grouped_sum S index (fun a => w a *
    ((prefixIndicator (hi a) q-prefixIndicator (lo a) q) *
      (1-prefixIndicator (cut (index a)) q)))
    (fun m => (floorKernel L R (m*q):ℂ))).symm

theorem coefficient_zero_of_masks_zero (S : Finset α) (index : α → ℕ)
    (w : α → ℂ) (lo hi : α → ℕ) (cut : ℕ → ℕ) (m q : ℕ)
    (hz : ∀ a ∈ S, index a = m →
      (prefixIndicator (hi a) q-prefixIndicator (lo a) q) *
        (1-prefixIndicator (cut (index a)) q) = 0) :
    maskedCoefficient S index w lo hi cut m q = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  obtain ⟨ha,he⟩ := Finset.mem_filter.mp ha
  rw [hz a ha he, mul_zero]

theorem rectangle_expansion (S : Finset α) (index : α → ℕ) (A B : Finset ℕ)
    (Q : ℕ) (w : α → ℂ) (lo hi : α → ℕ) (cut : ℕ → ℕ) (L R : ℝ)
    (hB : ∀ q ∈ B, q ≤ Q) :
    (∑ m ∈ A, ∑ q ∈ B,
      maskedCoefficient S index w lo hi cut m q * (floorKernel L R (m*q):ℂ)) =
      ∑ t : Mode Q, scalar Q t * productSum A B
        (modeCoefficient S index Q t w lo hi cut) (rightPhase Q t) L R := by
  calc
    _ = ∑ m ∈ A, ∑ q ∈ B, ∑ t : Mode Q,
        scalar Q t * (modeCoefficient S index Q t w lo hi cut m *
          rightPhase Q t q * (floorKernel L R (m*q):ℂ)) := by
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro q hq
      rw [coefficient_expansion S index Q w lo hi cut m q (hB q hq), Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = _ := by
      simp_rw [Finset.sum_comm (s := B) (t := Finset.univ)]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      simp only [productSum, Finset.mul_sum]

/-- Original mask vanishing justifies removal of inactive rectangles;
only then is each retained full Cartesian rectangle expanded into modes. -/
theorem maskedSum_eq_joint_modes (X : ℝ) (S : Finset α) (index : α → ℕ)
    (B : Finset ℕ) (relation : ℕ → ℕ → Prop) (Q : ℕ)
    (w : α → ℂ) (lo hi : α → ℕ) (cut : ℕ → ℕ) (L R : ℝ)
    (hX : 1 ≤ X)
    (hS : ∀ m ∈ support S index, 2 ≤ m ∧ (m:ℝ) ≤ X)
    (hB : ∀ q ∈ B, 2 ≤ q ∧ (q:ℝ) ≤ X)
    (hBQ : ∀ q ∈ B, q ≤ Q)
    (hzero : ∀ a ∈ S, ∀ q ∈ B, ¬relation (index a) q →
      (prefixIndicator (hi a) q-prefixIndicator (lo a) q) *
        (1-prefixIndicator (cut (index a)) q) = 0) :
    maskedSum S index B w lo hi cut L R =
      ∑ ij ∈ LongerTupleDyadic.jointFamily X (support S index) B relation,
        ∑ t : Mode Q, scalar Q t * productSum
          (block (support S index) 1 ij.1) (block B 1 ij.2)
          (modeCoefficient S index Q t w lo hi cut) (rightPhase Q t) L R := by
  rw [maskedSum_collected]
  rw [LongerTupleDyadic.sum_eq_sum_jointFamily_of_bounded X (support S index) B relation
    (fun m q => maskedCoefficient S index w lo hi cut m q * (floorKernel L R (m*q):ℂ))
    hX hS hB (by
      intro m _ q hq hnot
      rw [coefficient_zero_of_masks_zero S index w lo hi cut m q (by
        intro a ha he
        exact hzero a ha q hq (by simpa only [he] using hnot)), zero_mul])]
  apply Finset.sum_congr rfl
  intro ij _
  exact rectangle_expansion S index _ _ Q w lo hi cut L R
    (fun q hq => hBQ q (block_subset B 1 ij.2 hq))

run_cmd do
  for decl in [``coefficient_expansion, ``maskedSum_collected,
      ``coefficient_zero_of_masks_zero, ``rectangle_expansion, ``maskedSum_eq_joint_modes] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ORIGINAL MASK JOINT PARTITION BEFORE FOURIER EXPANSION PASSED"

end LongerTupleJointExpansion
