import PositiveInteriorCells
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-! The literal dyadic Mangoldt reciprocal model for the 253 rectangles.
The factor 8 in the third denominator is fixed conservative data.
The arithmetic lower bound on each reciprocal mass is an explicit premise;
it is not supplied by this module and no triple-count identity is claimed. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators
namespace PositiveInteriorModel
open PositiveInteriorRectangles PositiveInteriorCells

def mesh (X : ℝ) : ℝ := Real.log 2/Real.log X
def scale (m : ℕ) : ℝ := (2:ℝ)^m
def thirdScale (X : ℝ) (j : ℕ × ℕ) : ℝ := X/(scale j.1*scale j.2)
def denominator (X : ℝ) (j : ℕ × ℕ) : ℝ :=
  Real.log (2*scale j.1)*Real.log (2*scale j.2)*Real.log (8*thirdScale X j)
def reciprocalMass (a : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊2*a⌋₊, ArithmeticFunction.vonMangoldt n/(n:ℝ)
def cellModel (X : ℝ) (j : ℕ × ℕ) : ℝ :=
  reciprocalMass (scale j.1)*reciprocalMass (scale j.2)/denominator X j
def model (X : ℝ) : ℝ := ∑ j ∈ boxes (mesh X), cellModel X j

theorem mesh_pos (X : ℝ) (hX : 1 < X) : 0 < mesh X :=
  div_pos (Real.log_pos (by norm_num)) (Real.log_pos hX)

theorem mesh_mul_log (X : ℝ) (hX : 1 < X) : mesh X*Real.log X=Real.log 2 := by
  unfold mesh
  exact div_mul_cancel₀ _ (Real.log_pos hX).ne'

theorem three_product_bound (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x*y*z ≤ (x+y+z)^3/27 := by
  have h1 := mul_nonneg hx (sq_nonneg (y-z))
  have h2 := mul_nonneg (show 0 ≤ 4*(x+y+z)/3-x by linarith)
    (sq_nonneg (x-(x+y+z)/3))
  nlinarith

theorem denominator_identity (X : ℝ) (hX : 1 < X) (j : ℕ × ℕ) :
    denominator X j=(Real.log X)^3*
      (((j.1:ℝ)*mesh X+mesh X)*((j.2:ℝ)*mesh X+mesh X)*
        (1-(j.1:ℝ)*mesh X-(j.2:ℝ)*mesh X+3*mesh X)) := by
  have hp : 0 < scale j.1 := by unfold scale; positivity
  have hr : 0 < scale j.2 := by unfold scale; positivity
  have hL : 0 < thirdScale X j := div_pos (by linarith) (mul_pos hp hr)
  have hm := mesh_mul_log X hX
  have h8 : Real.log 8=3*Real.log 2 := by
    have hh := Real.log_pow (2:ℝ) 3
    norm_num at hh
    exact hh
  unfold denominator
  rw [Real.log_mul (by norm_num) hp.ne', Real.log_mul (by norm_num) hr.ne',
    Real.log_mul (by norm_num) hL.ne']
  rw [thirdScale, Real.log_div (by linarith : X ≠ 0) (mul_pos hp hr).ne',
    Real.log_mul hp.ne' hr.ne', scale, scale, Real.log_pow, Real.log_pow, h8]
  rw [← hm]
  ring

theorem denominator_bounds (X : ℝ) (hX : 1 < X) (hs : mesh X ≤ 1/1000000)
    (j : ℕ × ℕ) (hj : j ∈ boxes (mesh X)) :
    0 < denominator X j ∧
      denominator X j ≤ (Real.log X)^3*(1001/1000:ℝ)^3/27 := by
  have hm := mesh_pos X hX
  have hc := component_bounds _ _ (box_interior (mesh X) hm j hj)
  have hp : 0 < (j.1:ℝ)*mesh X+mesh X := by linarith [hc.1]
  have hr : 0 < (j.2:ℝ)*mesh X+mesh X := by linarith [hc.2.1]
  have hL : 0 < 1-(j.1:ℝ)*mesh X-(j.2:ℝ)*mesh X+3*mesh X := by
    linarith [hc.2.2]
  have hb := three_product_bound _ _ _ hp.le hr.le hL.le
  have he : ((j.1:ℝ)*mesh X+mesh X)+((j.2:ℝ)*mesh X+mesh X)+
      (1-(j.1:ℝ)*mesh X-(j.2:ℝ)*mesh X+3*mesh X)=1+5*mesh X := by ring
  rw [he] at hb
  have hu : (1+5*mesh X)^3 ≤ (1001/1000:ℝ)^3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  rw [denominator_identity X hX j]
  refine ⟨mul_pos (pow_pos (Real.log_pos hX) 3) (mul_pos (mul_pos hp hr) hL), ?_⟩
  have ht := hb.trans (div_le_div_of_nonneg_right hu (by norm_num))
  have hh := mul_le_mul_of_nonneg_left ht (pow_nonneg (Real.log_pos hX).le 3)
  simpa only [mul_div_assoc] using hh

theorem cell_model_lower (X : ℝ) (hX : 1 < X) (hs : mesh X ≤ 1/1000000)
    (j : ℕ × ℕ) (hj : j ∈ boxes (mesh X))
    (hp : (999/1000:ℝ)*Real.log 2 ≤ reciprocalMass (scale j.1))
    (hr : (999/1000:ℝ)*Real.log 2 ≤ reciprocalMass (scale j.2)) :
    27*(999/1000:ℝ)^2*(mesh X)^2/(1001/1000:ℝ)^3 ≤
      Real.log X*cellModel X j := by
  have hl := Real.log_pos hX
  have h2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hm := mesh_mul_log X hX
  have hd := denominator_bounds X hX hs j hj
  have hmn : ((999/1000:ℝ)*Real.log 2)^2 ≤
      reciprocalMass (scale j.1)*reciprocalMass (scale j.2) := by
    simpa only [pow_two] using mul_le_mul hp hr
      (by positivity : (0:ℝ) ≤ (999/1000)*Real.log 2) (by linarith)
  unfold cellModel
  rw [← mul_div_assoc, le_div_iff₀ hd.1]
  calc
    _ ≤ (27*(999/1000:ℝ)^2*(mesh X)^2/(1001/1000:ℝ)^3)*
        ((Real.log X)^3*(1001/1000:ℝ)^3/27) :=
      mul_le_mul_of_nonneg_left hd.2 (by positivity)
    _ = Real.log X*((999/1000:ℝ)*Real.log 2)^2 := by rw [← hm]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmn hl.le

theorem normalized_cell_mass_reserve (h : ℝ) (hh : 0 < h) (hs : h ≤ 1/1000000) :
    (141/1000:ℝ) < 27*(999/1000:ℝ)^2*((boxes h).card*h^2)/(1001/1000:ℝ)^3 := by
  have ha := (boxes_area_bounds h hh hs).1
  have hnum : (141/1000:ℝ) <
      27*(999/1000:ℝ)^2*(totalArea-16/1000000)/(1001/1000:ℝ)^3 := by
    rw [total_area_exact]
    norm_num
  apply hnum.trans_le
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  linarith

theorem model_lower_of_mass_reserve (X : ℝ) (hX : 1 < X) (hs : mesh X ≤ 1/1000000)
    (hmass : ∀ j ∈ boxes (mesh X),
      (999/1000:ℝ)*Real.log 2 ≤ reciprocalMass (scale j.1) ∧
      (999/1000:ℝ)*Real.log 2 ≤ reciprocalMass (scale j.2)) :
    (141/1000:ℝ)/Real.log X < model X := by
  have hh := Finset.sum_le_sum (fun j hj => cell_model_lower X hX hs j hj
    (hmass j hj).1 (hmass j hj).2)
  rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hh
  have he : ((boxes (mesh X)).card:ℝ)*
      (27*(999/1000:ℝ)^2*(mesh X)^2/(1001/1000:ℝ)^3)=
      27*(999/1000:ℝ)^2*((boxes (mesh X)).card*(mesh X)^2)/(1001/1000:ℝ)^3 := by ring
  rw [he] at hh
  apply (div_lt_iff₀ (Real.log_pos hX)).mpr
  have hc := (normalized_cell_mass_reserve (mesh X) (mesh_pos X hX) hs).trans_le hh
  simpa only [model, mul_comm] using hc

theorem model_lower_of_mass (X : ℝ) (hX : 1 < X) (hs : mesh X ≤ 1/1000000)
    (hmass : ∀ j ∈ boxes (mesh X),
      (999/1000:ℝ)*Real.log 2 ≤ reciprocalMass (scale j.1) ∧
      (999/1000:ℝ)*Real.log 2 ≤ reciprocalMass (scale j.2)) :
    (7/50:ℝ)/Real.log X < model X :=
  (div_lt_div_of_pos_right (by norm_num : (7/50:ℝ) < 141/1000) (Real.log_pos hX)).trans
    (model_lower_of_mass_reserve X hX hs hmass)

run_cmd do
  for decl in [``mesh_pos, ``mesh_mul_log, ``three_product_bound,
      ``denominator_identity, ``denominator_bounds, ``cell_model_lower,
      ``normalized_cell_mass_reserve, ``model_lower_of_mass_reserve,
      ``model_lower_of_mass] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL DYADIC MODEL >7/(50 LOG X), CONDITIONAL ON EXPLICIT RECIPROCAL MASSES; NO COUNT TRANSFER"
end PositiveInteriorModel
end
