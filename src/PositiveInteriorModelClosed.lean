import PositiveInteriorModel
import PositiveInteriorMass

/-! Unconditional eventual lower bound for the actual finite dyadic reciprocal
Mangoldt model on the 253 rectangles. This is a main-term model only: no
short-window triple-count approximation or high-frequency estimate is claimed. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators
namespace PositiveInteriorModel
open PositiveInteriorRectangles PositiveInteriorCells

theorem reciprocal_mass_eq (N : ℝ) :
    reciprocalMass N=Erdos374.PositiveInteriorMass.reciprocalMangoldtMass N := rfl

theorem log_scale_identity (X : ℝ) (hX : 1 < X) (m : ℕ) :
    Real.log (scale m)=((m:ℝ)*mesh X)*Real.log X := by
  rw [scale, Real.log_pow, ← mesh_mul_log X hX]
  ring

theorem scale_ge_of_exponent (X N : ℝ) (m : ℕ)
    (hX : 1 < X) (hN : 0 < N) (hlog : 4*Real.log N ≤ Real.log X)
    (hm : (1/4:ℝ) ≤ (m:ℝ)*mesh X) : N ≤ scale m := by
  have hp : 0 < scale m := by unfold scale; positivity
  have hl : Real.log N ≤ Real.log (scale m) := by
    rw [log_scale_identity X hX m]
    have hh := mul_le_mul_of_nonneg_right hm (Real.log_pos hX).le
    linarith
  have hh := Real.exp_le_exp.mpr hl
  simpa only [Real.exp_log hN, Real.exp_log hp] using hh

theorem eventual_model_lower_reserve :
    ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ X ≥ X0, (141/1000:ℝ)/Real.log X < model X := by
  obtain ⟨N0,hN01,hmass⟩ := Erdos374.PositiveInteriorMass.reciprocal_mass_bounds
  let Y : ℝ := max (1000000*Real.log 2) (4*Real.log N0)
  refine ⟨max 2 (Real.exp Y), le_max_left _ _, ?_⟩
  intro X hX
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
  have hX1 : 1 < X := by linarith
  have hY : Y ≤ Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos Y) ((le_max_right _ _).trans hX)
    simpa only [Real.log_exp] using hh
  have hbig : 1000000*Real.log 2 ≤ Real.log X := (le_max_left _ _).trans hY
  have hNlog : 4*Real.log N0 ≤ Real.log X := (le_max_right _ _).trans hY
  have hs : mesh X ≤ 1/1000000 := by
    unfold mesh
    apply (div_le_iff₀ (Real.log_pos hX1)).mpr
    linarith
  apply model_lower_of_mass_reserve X hX1 hs
  intro j hj
  have hc := component_bounds _ _ (box_interior (mesh X) (mesh_pos X hX1) j hj)
  have hp := scale_ge_of_exponent X N0 j.1 hX1 (by linarith) hNlog hc.1
  have hr := scale_ge_of_exponent X N0 j.2 hX1 (by linarith) hNlog hc.2.1
  rw [reciprocal_mass_eq, reciprocal_mass_eq]
  exact ⟨(hmass _ hp).1, (hmass _ hr).1⟩

theorem eventual_model_lower :
    ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ X ≥ X0, (7/50:ℝ)/Real.log X < model X := by
  obtain ⟨X0,hX0,hb⟩ := eventual_model_lower_reserve
  refine ⟨X0,hX0,?_⟩
  intro X hX
  have hX1 : 1 < X := by linarith
  exact (div_lt_div_of_pos_right (by norm_num : (7/50:ℝ) < 141/1000)
    (Real.log_pos hX1)).trans (hb X hX)

run_cmd do
  for decl in [``reciprocal_mass_eq, ``log_scale_identity, ``scale_ge_of_exponent,
      ``eventual_model_lower_reserve, ``eventual_model_lower] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL EVENTUAL DYADIC MANGOLDT MODEL >7/(50 LOG X); TRIPLE-COUNT TRANSFER OPEN"
end PositiveInteriorModel
end
