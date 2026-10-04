import Item1SourceGlue
import Item1QuadraticAssembly
import Item1SharpAtomMean

/-! UNCOMPILED, 2026-10-02. The physical bad-tuple budget is constructed from
actual factor masses. Its eventual endpoint takes no deletion estimate, PNT
estimate, cap, or small energy as an assumption. The prime-power mass theorem
it uses is elementary (psi-theta), not the PNT-based low-frequency theorem.
All earlier imported drafts must still compile before this is a formal result. -/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
namespace Item1PhysicalDeletion
open Item1SourceGlue Item1SelectedWindow Item1SelectedFourier Item1QuadraticAssembly
open SourceLiteralMoments SourceLiteralMass PositiveInteriorModel PositiveInteriorCells
open PositiveSharpMovingWindow
open PositiveSharpCounts
open CancellationTransferEndpoints CancellationTransferCenter

/-- A single geometric guard, independent of the changing source cell. -/
theorem mesh_of_log_guard (X : ℝ) (hX : 1<X) (hlog : 1000000≤Real.log X) :
    mesh X≤1/1000000 := by
  have hl : 0<Real.log X := Real.log_pos hX
  have hl2 : Real.log 2≤1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh
    exact hh
  have hmesh : mesh X≤1/Real.log X :=
    (le_div_iff₀ hl).mpr ((mesh_mul_log X hX).le.trans hl2)
  exact hmesh.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlog)

theorem eventually_geometry :
    ∀ᶠ X : ℝ in atTop, 2≤X ∧ 1000000≤Real.log X ∧ mesh X≤1/1000000 := by
  filter_upwards [eventually_ge_atTop (2:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000000:ℝ))] with X hX hl
  exact ⟨hX,hl,mesh_of_log_guard X (by linarith) hl⟩

/-- Exact window identity, valid before integration and retaining all indices. -/
theorem count_over_width_eq_atoms (X Y x : ℝ) (S : Finset SourceTriple)
    (heta : Y/X<1) :
    selectedCount S x (x*Y/X)/(x*Y/X)=
      ∑ a∈S, Item1SharpAtomMean.atom (Y/X) (tripleProduct a) (tripleWeight a) x := by
  classical
  unfold selectedCount
  rw [Finset.sum_filter,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  rw [Item1SharpAtomMean.atom_literal _ _ _ _ heta]
  have hh : x-x*Y/X=(1-Y/X)*x := by ring
  have hw : x*Y/X=(Y/X)*x := by ring
  unfold inWindow
  simp only [hh]
  simp only [hw]
  split_ifs <;> simp

/-- The literal bad-cell integral is bounded by its reciprocal tuple mass.
This includes products outside [X,2X] and coincident products. -/
theorem badCell_mean_le_mass (X Y : ℝ) (j : ℕ×ℕ) (hX : 1<X)
    (hj : j∈boxes (mesh X)) (hY : 0<Y) (hYX : Y≤X/2) :
    (∫ x in Icc X (2*X), badCell X Y j x)/X≤
      4*tupleMass (badTuples X j)/denominator X j := by
  have hXp : 0<X := by linarith
  have he0 : 0<Y/X := div_pos hY hXp
  have he2 : Y/X≤1/2 := (div_le_iff₀ hXp).mpr (by linarith)
  have he1 : Y/X<1 := by linarith
  have hd := cell_denominator_pos X j hX hj
  have hm := Item1SharpAtomMean.finite_first_mean (badTuples X j)
    tripleProduct tripleWeight X (Y/X) hXp he0 he2
    (fun a ha => SourceLogWindow.triple_positive X j a (badTuples_subset X j ha))
    (fun a _ => tripleWeight_nonneg a)
  have heq : badCell X Y j = fun x =>
      (∑ a∈badTuples X j,
        Item1SharpAtomMean.atom (Y/X) (tripleProduct a) (tripleWeight a) x)/
          denominator X j := by
    funext x
    rw [←count_over_width_eq_atoms X Y x (badTuples X j) he1]
    unfold badCell
    ring
  rw [heq,integral_div]
  have h := div_le_div_of_nonneg_right hm hd.le
  simpa only [tupleMass,div_div, mul_comm X (denominator X j)] using h

/-- One cell: both the width mean and the cell denominator are explicit. -/
theorem badCell_mean_le (X Y eps : ℝ) (j : ℕ×ℕ)
    (hX : 2≤X) (hlog : 1000000≤Real.log X) (hj : j∈boxes (mesh X))
    (hY : 0<Y) (hYX : Y≤X/2) (heps : 0≤eps)
    (hbad : ∀ i : Fin 3, Item1SourceLocalArithmetic.badMass X j i≤eps) :
    (∫ x in Icc X (2*X), badCell X Y j x)/X≤259200*eps/(Real.log X)^3 := by
  have hX1 : 1<X := by linarith
  have hl : 0<Real.log X := by linarith
  have hd := cell_denominator_pos X j hX1 hj
  have hbase : 0<(Real.log X)^3/96 := by positivity
  calc
    _ ≤ 4*tupleMass (badTuples X j)/denominator X j :=
      badCell_mean_le_mass X Y j hX1 hj hY hYX
    _ ≤ 2700*eps/denominator X j := div_le_div_of_nonneg_right
      (by linarith [bad_tupleMass_bound X eps j hX hlog hj hbad]) hd.le
    _ ≤ 2700*eps/((Real.log X)^3/96) :=
      div_le_div_of_nonneg_left (by positivity) hbase (denominator_lower X hX1 j hj)
    _ = _ := by ring

/-- Actual growing cell family: its cardinality is not replaced by 253. -/
theorem badMean_le (X Y eps : ℝ) (hX : 2≤X) (hlog : 1000000≤Real.log X)
    (hm : mesh X≤1/1000000) (hY : 0<Y) (hYX : Y≤X/2) (heps : 0≤eps)
    (hbad : ∀ j∈boxes (mesh X), ∀ i : Fin 3,
      Item1SourceLocalArithmetic.badMass X j i≤eps) :
    badMean X Y≤5760*eps/Real.log X := by
  have hX1 : 1<X := by linarith
  have hl : 0<Real.log X := by linarith
  unfold badMean
  rw [integral_finsetSum _ (fun j hj => badCell_integrable X Y j hX1 hj hY hYX),
    Finset.sum_div]
  have hsum := Finset.sum_le_sum (fun j hj =>
    badCell_mean_le X Y eps j hX hlog hj hY hYX heps (hbad j hj))
  simp only [Finset.sum_const,nsmul_eq_mul] at hsum
  have hc := mul_le_mul_of_nonneg_right (cell_card_normalized_bound X hX1 hm)
    (show 0≤259200*eps/Real.log X by positivity)
  calc
    _ ≤ ((boxes (mesh X)).card:ℝ)*(259200*eps/(Real.log X)^3) := hsum
    _ = (((boxes (mesh X)).card:ℝ)/(Real.log X)^2)*
        (259200*eps/Real.log X) := by ring
    _ ≤ (1/45)*(259200*eps/Real.log X) := hc
    _ = _ := by ring

/-- The deletion budget is supplied internally, for ALL admissible widths.
The fixed eps=1/23040 is chosen before X, every cell, and Y. -/
theorem eventually_badMean_budget :
    ∀ᶠ X : ℝ in atTop, ∀ Y : ℝ, 0<Y → Y≤X/2 →
      badMean X Y≤1/(4*(Real.log X)^2) := by
  have hbad := Item1SourceLocalArithmetic.eventually_badMass_weighted 1
    (1/23040) (by norm_num)
  filter_upwards [eventually_geometry,hbad] with X hg hb
  obtain ⟨hX,hl,hm⟩ := hg
  have hlp : 0<Real.log X := by linarith
  have hLp : 0<1+Real.log X := by linarith
  let eps : ℝ := (1/23040)/(1+Real.log X)
  have hb' (j : ℕ×ℕ) (hj : j∈boxes (mesh X)) (i : Fin 3) :
      Item1SourceLocalArithmetic.badMass X j i≤eps := by
    exact (le_div_iff₀ hLp).mpr (by simpa only [pow_one] using hb j hj i)
  intro Y hY hYX
  calc
    _ ≤ 5760*eps/Real.log X := badMean_le X Y eps hX hl hm hY hYX (by dsimp [eps]; positivity) hb'
    _ = 1/(4*Real.log X*(1+Real.log X)) := by
      dsimp [eps]
      field_simp [hlp.ne',hLp.ne'] <;> ring
    _ ≤ 1/(4*(Real.log X)^2) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith

/-- Strictly fewer premises than the preceding two-budget adapter.
Only the actual normalized total-energy bound remains quantitative. -/
theorem eventually_literal_item1_of_energy :
    ∀ᶠ X : ℝ in atTop, ∀ Y : ℝ, 0<Y → Y≤X/2 →
      totalEnergy X Y≤1/1024 →
      (∫ x in Icc X (2*X), sourceResidualAbs X x (x*Y/X))/X≤1/(Real.log X)^2 := by
  filter_upwards [eventually_geometry,eventually_badMean_budget] with X hg hb
  intro Y hY hYX hE
  exact literal_item1_of_two_budgets X Y hg.1 hg.2.1 hg.2.2 hY hYX hE (hb Y hY hYX)

end Item1PhysicalDeletion

-- ROOT SOURCE RECURSIVE AUDIT: exact original declarations.
run_cmd do
  for target in [
    ``Item1PhysicalDeletion.mesh_of_log_guard,
    ``Item1PhysicalDeletion.eventually_geometry,
    ``Item1PhysicalDeletion.count_over_width_eq_atoms,
    ``Item1PhysicalDeletion.badCell_mean_le_mass,
    ``Item1PhysicalDeletion.badCell_mean_le,
    ``Item1PhysicalDeletion.badMean_le,
    ``Item1PhysicalDeletion.eventually_badMean_budget,
    ``Item1PhysicalDeletion.eventually_literal_item1_of_energy] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1PhysicalDeletion: 8 original theorem guards passed."
