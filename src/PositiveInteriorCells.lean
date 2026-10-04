import PositiveInteriorRectangles
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Order.Interval.Finset.Nat

/-! Actual full mesh cells inside the 253 certified positive rectangles.
The elementary floor/ceil count is the same construction as PositiveCells161,
reproved here with narrow imports in the isolated current dependency closure.
No Mangoldt mass or prime-count assertion is made in this component. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators
namespace PositiveInteriorCells
open PositiveInteriorRectangles

def cellIndices (h a b : ℝ) : Finset ℕ := Finset.Ico ⌈a/h⌉₊ ⌊b/h⌋₊
def cells (h : ℝ) (i : ℕ) : Finset (ℕ × ℕ) :=
  cellIndices h (left i) (right i) ×ˢ cellIndices h (lower i) (upper i)
def boxes (h : ℝ) : Finset (ℕ × ℕ) := (Finset.range 253).biUnion (cells h)
def boundaryCost : ℝ :=
  ∑ i ∈ Finset.range 253, 2*((right i-left i)+(upper i-lower i))

theorem index_endpoints (h a b : ℝ) (hh : 0 < h) (ha : 0 ≤ a) (hab : a ≤ b)
    (m : ℕ) (hm : m ∈ cellIndices h a b) :
    a ≤ (m:ℝ)*h ∧ ((m:ℝ)+1)*h ≤ b := by
  have hm' := Finset.mem_Ico.mp hm
  have hlo : a/h ≤ (⌈a/h⌉₊:ℝ) := Nat.le_ceil _
  have hhi : (⌊b/h⌋₊:ℝ) ≤ b/h := Nat.floor_le (div_nonneg (ha.trans hab) hh.le)
  have hmlo : (⌈a/h⌉₊:ℝ) ≤ m := by exact_mod_cast hm'.1
  have hmhi : (m:ℝ)+1 ≤ (⌊b/h⌋₊:ℝ) := by
    exact_mod_cast (Nat.add_one_le_iff.mpr hm'.2)
  exact ⟨(div_le_iff₀ hh).mp (hlo.trans hmlo),
    (le_div_iff₀ hh).mp (hmhi.trans hhi)⟩

theorem cell_count_bounds (h a b : ℝ) (hh : 0 < h) (ha : 0 ≤ a)
    (hwidth : 2*h ≤ b-a) :
    b-a-2*h ≤ (cellIndices h a b).card*h ∧
      (cellIndices h a b).card*h ≤ b-a := by
  have hb : 0 ≤ b := by linarith
  have hl1 : a ≤ (⌈a/h⌉₊:ℝ)*h := (div_le_iff₀ hh).mp (Nat.le_ceil (a/h))
  have hl2 : (⌈a/h⌉₊:ℝ)*h < a+h := by
    have he := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (div_nonneg ha hh.le)) hh
    convert he using 1
    field_simp
  have hu1 : (⌊b/h⌋₊:ℝ)*h ≤ b :=
    (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg hb hh.le))
  have hu2 : b < (⌊b/h⌋₊:ℝ)*h+h := by
    have he := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one (b/h)) hh
    convert he using 1
    all_goals field_simp
  have hordR : (⌈a/h⌉₊:ℝ) ≤ (⌊b/h⌋₊:ℝ) :=
    le_of_mul_le_mul_right (by linarith) hh
  have hord : ⌈a/h⌉₊ ≤ ⌊b/h⌋₊ := by exact_mod_cast hordR
  unfold cellIndices
  rw [Nat.card_Ico, Nat.cast_sub hord, sub_mul]
  constructor <;> linarith

theorem left_nonneg (i : ℕ) : 0 ≤ left i := by
  unfold left start
  have hp := step_pos
  positivity

theorem lower_nonneg (i : ℕ) (hi : i < 253) : 0 ≤ lower i := by
  have hb := (endpoint_bounds i hi).2
  have ho := (endpoints_ordered i).1
  unfold lower finish at *
  linarith

theorem cells_disjoint (h : ℝ) (hh : 0 < h) (i j : ℕ) (hij : i ≠ j) :
    Disjoint (cells h i) (cells h j) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hi := index_endpoints h (left i) (right i) hh (left_nonneg i)
    (endpoints_ordered i).1.le p.1
    (Finset.mem_product.mp hp).1
  have hj := index_endpoints h (left j) (right j) hh (left_nonneg j)
    (endpoints_ordered j).1.le p.1
    (Finset.mem_product.mp hq).1
  rcases lt_or_gt_of_ne hij with h | h
  · have hb := right_le_left i j h
    nlinarith [hi.2,hj.1]
  · have hb := right_le_left j i h
    nlinarith [hj.2,hi.1]

theorem boxes_card (h : ℝ) (hh : 0 < h) :
    (boxes h).card=∑ i ∈ Finset.range 253, (cells h i).card := by
  apply Finset.card_biUnion
  intro i _ j _ hij
  exact cells_disjoint h hh i j hij

theorem box_interior (h : ℝ) (hh : 0 < h) (p : ℕ × ℕ) (hp : p ∈ boxes h) :
    interior ((p.1:ℝ)*h) ((p.2:ℝ)*h) := by
  obtain ⟨i,hi,hp⟩ := Finset.mem_biUnion.mp hp
  have hi' := Finset.mem_range.mp hi
  have hu := index_endpoints h (left i) (right i) hh (left_nonneg i)
    (endpoints_ordered i).1.le p.1
    (Finset.mem_product.mp hp).1
  have hv := index_endpoints h (lower i) (upper i) hh (lower_nonneg i hi')
    (endpoints_ordered i).2.le p.2
    (Finset.mem_product.mp hp).2
  exact closed_rectangle_subset i hi' _ _ ⟨hu.1, by nlinarith [hu.2]⟩
    ⟨hv.1, by nlinarith [hv.2]⟩

theorem small_mesh_widths (h : ℝ) (hh : h ≤ 1/1000000) (i : ℕ) :
    2*h ≤ right i-left i ∧ 2*h ≤ upper i-lower i := by
  rw [width_eq, height_eq]
  have hi : 0 ≤ (i:ℝ) := Nat.cast_nonneg _
  have hd : (1/1000000:ℝ)*6 ≤ step := by norm_num [step,finish,start]
  have hm := mul_nonneg hi step_pos.le
  constructor <;> nlinarith

theorem cell_area_bounds (h : ℝ) (hh : 0 < h) (hs : h ≤ 1/1000000)
    (i : ℕ) (hi : i < 253) :
    area i-2*h*((right i-left i)+(upper i-lower i)) ≤ (cells h i).card*h^2 ∧
      (cells h i).card*h^2 ≤ area i := by
  have hw := small_mesh_widths h hs i
  have hx := cell_count_bounds h (left i) (right i) hh (left_nonneg i) hw.1
  have hy := cell_count_bounds h (lower i) (upper i) hh (lower_nonneg i hi) hw.2
  let x : ℝ := (cellIndices h (left i) (right i)).card*h
  let y : ℝ := (cellIndices h (lower i) (upper i)).card*h
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have he : (cells h i).card*h^2=x*y := by
    unfold cells
    rw [Finset.card_product, Nat.cast_mul]
    dsimp [x,y]
    ring
  have hl := mul_le_mul hx.1 hy.1 (by linarith : 0 ≤ upper i-lower i-2*h) hx0
  have hu := mul_le_mul hx.2 hy.2 hy0 (by linarith : 0 ≤ right i-left i)
  change (right i-left i-2*h)*(upper i-lower i-2*h) ≤ x*y at hl
  change x*y ≤ (right i-left i)*(upper i-lower i) at hu
  rw [he]
  unfold area
  exact ⟨by nlinarith [sq_nonneg h],hu⟩

theorem boundary_cost_exact : boundaryCost=(2068781/134400:ℝ) := by
  unfold boundaryCost
  simp_rw [width_eq, height_eq]
  have he : (∑ i ∈ Finset.range 253, 2*(step+((i:ℝ)+1)*step/3)) =
      253*(2*step)+(2*step/3)*(∑ i ∈ Finset.range 253, ((i:ℝ)+1)) := by
    calc
      _ = ∑ i ∈ Finset.range 253, (2*step+(2*step/3)*((i:ℝ)+1)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]; norm_num
  rw [he, sum_successor]
  norm_num [step,finish,start]

theorem area_sum_identity (h : ℝ) (hh : 0 < h) :
    (∑ i ∈ Finset.range 253, (cells h i).card*h^2)=(boxes h).card*h^2 := by
  rw [boxes_card h hh, Nat.cast_sum, Finset.sum_mul]

theorem boxes_area_bounds (h : ℝ) (hh : 0 < h) (hs : h ≤ 1/1000000) :
    totalArea-16*h ≤ (boxes h).card*h^2 ∧ (boxes h).card*h^2 ≤ totalArea := by
  have hl := Finset.sum_le_sum (fun i hi => (cell_area_bounds h hh hs i
    (Finset.mem_range.mp hi)).1)
  have hu := Finset.sum_le_sum (fun i hi => (cell_area_bounds h hh hs i
    (Finset.mem_range.mp hi)).2)
  rw [area_sum_identity h hh] at hl hu
  have he : (∑ i ∈ Finset.range 253,
      (area i-2*h*((right i-left i)+(upper i-lower i))))=totalArea-h*boundaryCost := by
    unfold totalArea boundaryCost
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, boundary_cost_exact] at hl
  exact ⟨by linarith,hu⟩

theorem finite_mesh_scalar_margin :
    (7/50:ℝ) < 27*(999/1000:ℝ)^2*(totalArea-16/1000000)/(1001/1000:ℝ)^3 := by
  rw [total_area_exact]
  norm_num

theorem normalized_cell_mass_lower (h : ℝ) (hh : 0 < h) (hs : h ≤ 1/1000000) :
    (7/50:ℝ) < 27*(999/1000:ℝ)^2*((boxes h).card*h^2)/(1001/1000:ℝ)^3 := by
  have ha := (boxes_area_bounds h hh hs).1
  apply finite_mesh_scalar_margin.trans_le
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  linarith

run_cmd do
  for decl in [``index_endpoints, ``cell_count_bounds, ``left_nonneg, ``lower_nonneg,
      ``cells_disjoint, ``boxes_card, ``box_interior, ``small_mesh_widths,
      ``cell_area_bounds, ``boundary_cost_exact, ``area_sum_identity,
      ``boxes_area_bounds, ``finite_mesh_scalar_margin, ``normalized_cell_mass_lower] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL DISJOINT DYADIC CELL COUNTS AND FINITE MESH BUDGET; NO MANGOLDT TRANSFER"
end PositiveInteriorCells
end
