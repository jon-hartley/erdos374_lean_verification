import SingletonDivisor
import SingletonResidue

/-! Exact unit-cell reduction of real floors to finite Euclidean counts. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SingletonCells

theorem floor_cell (q : ℤ) (v : ℝ) (a : ℕ) (hv : 0≤v ∧ v<1) :
    ⌊((q:ℝ)+v)/a⌋ = q/(a:ℤ) := by
  rw [Int.floor_div_natCast, Int.floor_intCast_add,
    Int.floor_eq_zero_iff.mpr hv, add_zero]

theorem floor_shift_cell (q k : ℤ) (v u : ℝ) (a : ℕ)
    (hv : 0≤v ∧ v<1) (hu : 0≤u ∧ u<1) :
    ⌊((q:ℝ)+v-((k:ℝ)+u))/a⌋ =
      (q-(if v<u then k+1 else k))/(a:ℤ) := by
  split_ifs with h
  · have hv' : 0≤v-u+1 ∧ v-u+1<1 := by constructor <;> linarith
    have heq : (q:ℝ)+v-((k:ℝ)+u)=((q-(k+1):ℤ):ℝ)+(v-u+1) := by push_cast; ring
    rw [heq]
    exact floor_cell (q-(k+1)) (v-u+1) a hv'
  · have hv' : 0≤v-u ∧ v-u<1 := by constructor <;> linarith
    have heq : (q:ℝ)+v-((k:ℝ)+u)=((q-k:ℤ):ℝ)+(v-u) := by push_cast; ring
    rw [heq]
    exact floor_cell (q-k) (v-u) a hv'

theorem discrepancy_cell (a q : ℕ) (k : ℤ) (v u : ℝ)
    (hv : 0≤v ∧ v<1) (hu : 0≤u ∧ u<1) :
    SingletonDivisor.discrepancy a ((q:ℝ)+v) ((k:ℝ)+u) =
      (SingletonResidue.count a (if v<u then k+1 else k) q:ℝ) - ((k:ℝ)+u)/a := by
  unfold SingletonDivisor.discrepancy SingletonResidue.count
  rw [show ((q:ℝ)+v) = (((q:ℕ):ℤ):ℝ)+v by simp,
    floor_cell (q:ℤ) v a hv, floor_shift_cell (q:ℤ) k v u a hv hu]
  push_cast
  rfl

end SingletonCells
