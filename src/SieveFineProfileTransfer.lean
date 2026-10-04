import SieveFineProfileStructure
import UpperProfileGridSoundness
import SieveUpperProfileBound

/-! Transfer literal fine-grid rectangle budgets to the actual two-prime
recurrence and then the full upper selector. The numeric row budgets are
explicit parameters here; the final certificate must instantiate them. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real
open scoped BigOperators
namespace SieveFineProfileTransfer
open SieveFineProfileStructure SieveStoppingTwoStep UpperProfileGridArithmetic

def rowBudget (v : ℕ → ℝ) (i : ℕ) : ℝ :=
  UpperProfileGridSoundness.forcingRectangles i+
    (∑ j ∈ Finset.range 720,
      coefficient v j*UpperProfileGridSoundness.cumulativeRectangles i j)+
    1/10000+1/100000

theorem edge_eq (k : ℕ) :
    SieveProfileOperatorGrid.edge (1/400:ℝ) k = UpperProfileGridSoundness.edge k := by
  unfold SieveProfileOperatorGrid.edge UpperProfileGridSoundness.edge
  ring

theorem rowBudget_eq (v : ℕ → ℝ) (i : ℕ) :
    SieveProfileTransition.rowBound (Finset.range 720) (coefficient v) cut
      (rowPoint i) (1/400) (forcingCount i) (outerCount i)+1/100000 = rowBudget v i := by
  simp only [SieveProfileTransition.rowBound, rowBudget,
    SieveForcingProfileRectangles.rectangles, SieveForcingProfileScalar.kernel,
    UpperProfileGridSoundness.forcingRectangles, UpperProfileGridSoundness.cumulativeRectangles,
    SieveProfileOperatorCumulative.shape, UpperProfileGridSoundness.kernel,
    SieveProfileOperatorGrid.edge, UpperProfileGridSoundness.edge,
    UpperProfileGridSoundness.rowPoint, rowPoint, UpperProfileGridSoundness.cut, cut,
    div_eq_mul_inv, one_mul]

theorem actual_row (v : ℕ → ℝ) (hd : ∀ j < 720, 0 ≤ coefficient v j)
    (i : ℕ) (hbudget : rowBudget v i ≤ v i) :
    ∃ B : ℝ, 2 ≤ B ∧ ∀ z T : ℝ, B ≤ z → z^2 ≤ T →
      rowPoint i ≤ log T/log z →
      forcing T z+operator (fun T z => profile v (log T/log z)) T z ≤ v i := by
  have hr : 2 ≤ rowPoint i := by
    unfold rowPoint
    have hi : 0 ≤ (i:ℝ) := Nat.cast_nonneg i
    linarith
  have hfc : 4/rowPoint i ≤ 1+(forcingCount i:ℝ)*(1/400) := by
    simpa only [rowPoint, UpperProfileGridSoundness.rowPoint, div_eq_mul_inv, one_mul]
      using UpperProfileGridSoundness.forcing_coverage i
  have hfl : ∀ k < forcingCount i, 1+(k:ℝ)*(1/400) ≤ 4/rowPoint i := by
    intro k hk
    simpa only [rowPoint, UpperProfileGridSoundness.rowPoint,
      UpperProfileGridSoundness.edge, div_eq_mul_inv, one_mul]
      using UpperProfileGridSoundness.forcing_left i k hk
  have hcc : ∀ j ∈ Finset.range 720,
      cut j+2 ≤ rowPoint i*SieveProfileOperatorGrid.edge (1/400) (outerCount i j) := by
    intro j hj
    rw [edge_eq]
    exact UpperProfileGridSoundness.cumulative_coverage i j
  obtain ⟨B, hB, hb⟩ := SieveProfileTransition.eventually_transition
    (Finset.range 720) (coefficient v) cut (rowPoint i) (1/400)
    (forcingCount i) (outerCount i) hr (by norm_num)
    (fun j hj => hd j (Finset.mem_range.mp hj)) (fun j _ => cut_ge_two j)
    hfc hfl hcc (1/100000) (by norm_num)
  refine ⟨B, hB, ?_⟩
  intro z T hz hT hr
  have h := hb z T hz hT hr
  rw [rowBudget_eq] at h
  exact h.trans hbudget

theorem actual_postfixed (v : ℕ → ℝ)
    (hd : ∀ j < 720, 0 ≤ coefficient v j) (hN : v 720 = 0)
    (hbudget : ∀ i < 720, rowBudget v i ≤ v i) :
    SieveProfileSupersolution.Postfixed (profile v) :=
  postfixed_of_rows v hd hN (fun i hi => actual_row v hd i (hbudget i hi))

theorem eventual_upper_bound (v : ℕ → ℝ)
    (hd : ∀ j < 720, 0 ≤ coefficient v j) (hN : v 720 = 0)
    (hbudget : ∀ i < 720, rowBudget v i ≤ v i)
    (harea : (∑ j ∈ Finset.range 720, v j)/40 ≤ (307/500:ℝ)) :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z T : ℝ, Z ≤ z → z^3 ≤ T →
      SieveFullCutoffTransfer.fullUpper T z ≤
        (452/375:ℝ)*SieveStoppingExpansion.primeEuler z := by
  have hpost := actual_postfixed v hd hN hbudget
  obtain ⟨Z, hZ, hb⟩ := SieveUpperProfileBound.eventually_upper_of_postfixed
    (Finset.range 720) (coefficient v) cut
    (fun j hj => hd j (Finset.mem_range.mp hj)) (fun j _ => cut_ge_two j)
    hpost (1/10000) (by norm_num)
  refine ⟨Z, hZ, ?_⟩
  intro z T hz hT
  have h := hb z T hz hT
  rw [area_eq v hN] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith)
    (SieveEulerRatio.euler_pos z).le)

run_cmd do
  for decl in [``edge_eq, ``rowBudget_eq, ``actual_row, ``actual_postfixed,
      ``eventual_upper_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "LITERAL FINE-GRID ROWS TRANSFER TO ACTUAL POSTFIXED AND UPPER SELECTOR"
end SieveFineProfileTransfer
end
