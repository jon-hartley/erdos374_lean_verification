import OuterBufferedSourceWork

/-! The nine buffered cutoffs are exactly the nine source log inequalities.
Thus the polynomial gap proved for the retained source applies to the
actual mask, not just to an unrelated set of candidate thresholds. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section

namespace OuterBufferedLogMaskWork
open OuterSourceReindexWork OuterBufferedSourceWork OuterSeparatedLogMaskWork
open SieveGeometricGrid

def thresholdCuts (v : ℝ) (z : Fin 9→ℝ) : Prop :=
  v < z 0 ∧ z 1 ≤ v ∧ v < z 2 ∧ z 3 ≤ v ∧ z 4 ≤ v ∧
    v < z 5 ∧ z 6 ≤ v ∧ v < z 7 ∧ z 8 < v

theorem affine_lower_iff (c H v w : ℝ) (hc : 0<c) :
    c*H ≤ c*v+w ↔ H-w/c ≤ v := by
  have hh := div_mul_cancel₀ w (ne_of_gt hc)
  constructor <;> intro he <;> nlinarith

theorem affine_upper_iff (c H v w : ℝ) (hc : 0<c) :
    c*v+w < c*H ↔ v < H-w/c := by
  have hh := div_mul_cancel₀ w (ne_of_gt hc)
  constructor <;> intro he <;> nlinarith

theorem logMask_iff_thresholdCuts (X s : ℝ) (u : Slice) (i j p : ℕ) (hs : 0<s) :
    logMask X s u.1 u.2.1 u.2.2 i j p ↔
      thresholdCuts (Real.log (p:ℝ)) (cutoffLogs X s u i j) := by
  have hs2 : 0<s^2 := sq_pos_of_pos hs
  have he (n : ℕ) : 0<exponent s n := by unfold exponent ratio; positivity
  dsimp [logMask,poolCuts,boxCuts,thresholdCuts,cutoffLogs]
  rw [affine_lower_iff _ _ _ _ hs2,affine_lower_iff _ _ _ _ hs2,
    affine_lower_iff _ _ _ _ (he i),affine_upper_iff _ _ _ _ (he (i+1)),
    affine_lower_iff _ _ _ _ (he j),affine_upper_iff _ _ _ _ (he (j+1))]
  have hlast : (26/35:ℝ)*Real.log X <
      Real.log (p:ℝ)+Real.log (u.1:ℝ)+Real.log (u.2.1:ℝ)+Real.log (u.2.2:ℝ) ↔
      (26/35:ℝ)*Real.log X-Real.log (u.1:ℝ)-Real.log (u.2.1:ℝ)-Real.log (u.2.2:ℝ) <
        Real.log (p:ℝ) := by constructor <;> intro hh <;> linarith
  rw [hlast]
  simp only [←lt_sub_iff_add_lt,and_assoc]

run_cmd do
  for decl in [``affine_lower_iff, ``affine_upper_iff, ``logMask_iff_thresholdCuts] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterBufferedLogMaskWork
