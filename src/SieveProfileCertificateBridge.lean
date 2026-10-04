import ProfileCertificateIndexed
import ProfileCertificateRectangleTables
import SieveProfileTransition
import SieveProfileStaircase

/-! The literal integer certificate bounds the actual forcing and two-prime
operator, with a positive error allowance and a common eventual threshold. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Real
open scoped BigOperators
namespace SieveProfileCertificateBridge
open ProfileCertificateArithmetic ProfileCertificateIndexed
open ProfileCertificateRectangles ProfileCertificateRectangleTables
open SieveStoppingTwoStep

def certifiedProfile (n : ℕ) : ℝ → ℝ := SieveProfileStaircase.profile 90 (value n)

theorem left_eq_rowPoint (i : ℕ) : SieveProfileStaircase.left i = rowPoint i := by
  unfold SieveProfileStaircase.left rowPoint
  ring

theorem cut_eq_childPoint (i : ℕ) : SieveProfileStaircase.cut i = childPoint i := by
  unfold SieveProfileStaircase.cut childPoint
  ring

theorem edge_eq_outerPoint (k : ℕ) :
    SieveProfileOperatorGrid.edge (1/50:ℝ) k = outerPoint k := by
  unfold SieveProfileOperatorGrid.edge outerPoint
  ring

theorem forcing_rectangles_eq (i : ℕ) :
    SieveForcingProfileRectangles.rectangles (rowPoint i) (1/50:ℝ) (forcingCount i) =
      forcingRectangles i := by
  simp only [SieveForcingProfileRectangles.rectangles, forcingRectangles,
    SieveForcingProfileScalar.kernel, outerPoint, div_eq_mul_inv, one_mul]

theorem cumulative_rectangles_eq (i j : ℕ) :
    (1/50:ℝ)*(∑ k ∈ Finset.range (outerCount i j),
      SieveProfileOperatorCumulative.shape (childPoint j)
        (rowPoint i*SieveProfileOperatorGrid.edge (1/50:ℝ) k-1)) =
      cumulativeRectangles i j := by
  simp only [edge_eq_outerPoint, SieveProfileOperatorCumulative.shape,
    cumulativeRectangles, cumulativeKernel]

theorem transition_profile_eq (n : ℕ) :
    SieveProfileTransition.profile (Finset.range 90) (coefficient n) childPoint =
      certifiedProfile n := by
  funext r
  simp only [SieveProfileTransition.profile, SieveProfileTransition.staircase,
    certifiedProfile, SieveProfileStaircase.profile, SieveProfileStaircase.staircase,
    coefficient, cut_eq_childPoint]

theorem actual_row (n : Fin 10) (i : Fin 90) :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^2 ≤ T →
      SieveProfileStaircase.left i.val ≤ log T/log z →
      forcing T z+operator (fun T z => certifiedProfile n.val (log T/log z)) T z ≤
        value (n.val+1) i.val := by
  have hn : n.val < 11 := by omega
  have hr : 2 ≤ rowPoint i.val := by
    unfold rowPoint
    have := Nat.cast_nonneg (α := ℝ) i.val
    linarith
  have hd : ∀ j ∈ Finset.range 90, 0 ≤ coefficient n.val j := by
    intro j hj
    exact coefficient_nonneg ⟨n.val, hn⟩ ⟨j, Finset.mem_range.mp hj⟩
  have hc : ∀ j ∈ Finset.range 90, 2 ≤ childPoint j := by
    intro j _
    unfold childPoint
    have := Nat.cast_nonneg (α := ℝ) j
    linarith
  have hfcover : 4/rowPoint i.val ≤ 1+(forcingCount i.val:ℝ)*(1/50:ℝ) := by
    simpa only [div_eq_mul_inv, one_mul] using forcing_coverage i.val (forces_literal i).2.2
  have hflast : ∀ k < forcingCount i.val, 1+(k:ℝ)*(1/50:ℝ) ≤ 4/rowPoint i.val := by
    simpa only [outerPoint, div_eq_mul_inv, one_mul] using forcing_last i.val (forces_literal i).2.1
  have hcover : ∀ j ∈ Finset.range 90, childPoint j+2 ≤
      rowPoint i.val*SieveProfileOperatorGrid.edge (1/50:ℝ) (outerCount i.val j) := by
    intro j hj
    have h := outer_coverage i.val j (all_rows_literal i ⟨j, Finset.mem_range.mp hj⟩).2.2
    have hp : 0 < rowPoint i.val := by linarith
    have h' := (div_le_iff₀ hp).mp h
    rw [edge_eq_outerPoint]
    unfold outerPoint
    nlinarith
  obtain ⟨Z, hZ, hb⟩ := SieveProfileTransition.eventually_transition
    (Finset.range 90) (coefficient n.val) childPoint (rowPoint i.val) (1/50:ℝ)
    (forcingCount i.val) (outerCount i.val) hr (by norm_num) hd hc hfcover hflast hcover
    (1/100000:ℝ) (by norm_num)
  refine ⟨Z, hZ, ?_⟩
  intro z T hz hT hratio
  rw [left_eq_rowPoint] at hratio
  have ha := hb z T hz hT hratio
  rw [transition_profile_eq] at ha
  apply ha.trans
  have hf : forcingRectangles i.val ≤ forceValue i.val := by
    simpa only [forceValue, forceEntry, scale, Nat.cast_ofNat] using forcing_bound i
  have hs : (∑ j ∈ Finset.range 90, coefficient n.val j*cumulativeRectangles i.val j) ≤
      ∑ j ∈ Finset.range 90, matrixValue i.val j*coefficient n.val j := by
    apply Finset.sum_le_sum
    intro j hj
    have h := mul_le_mul_of_nonneg_left (cumulative_bound i ⟨j, Finset.mem_range.mp hj⟩) (hd j hj)
    simpa only [matrixValue, matrixEntry, scale, Nat.cast_ofNat, mul_comm] using h
  unfold SieveProfileTransition.rowBound
  simp only [forcing_rectangles_eq, cumulative_rectangles_eq]
  have hbudget := real_step n i
  linarith

run_cmd do
  for decl in [``certifiedProfile, ``left_eq_rowPoint, ``cut_eq_childPoint,
    ``edge_eq_outerPoint, ``forcing_rectangles_eq, ``cumulative_rectangles_eq,
    ``transition_profile_eq, ``actual_row] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "RATIONAL CERTIFICATE CONNECTED TO ACTUAL PRIME-SUM PROFILE ROWS"
end SieveProfileCertificateBridge
end
