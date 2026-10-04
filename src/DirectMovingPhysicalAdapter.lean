import MomentRemainderSupport
import MomentSmallMean
import SingletonActualApplication

/-! Exact zero extension and natural/integer floor adapter for the complete
signed physical remainder through X^.545. All original coefficients remain. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace DirectMovingPhysicalAdapter
open MomentSmallRemainder PositiveSharpRemainderAnalysisPhysical

def lowCoefficient (X s : ℝ) (n : ℕ) : ℝ :=
  if n ∈ lowSupport X s (109/200) then coefficient X s n else 0

theorem support_subset (X s : ℝ)
    (hpos : ∀n∈support X s, 0<n) :
    lowSupport X s (109/200) ⊆ Finset.Icc 1 ⌊X^(109/200:ℝ)⌋₊ := by
  intro n hn
  obtain ⟨hn,hbound⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_Icc.mpr ⟨hpos n hn,Nat.le_floor hbound⟩

theorem coefficient_cap (X s B : ℝ) (hB : 0≤B)
    (hcap : ∀n∈support X s, |coefficient X s n|≤B) (n : ℕ) :
    |lowCoefficient X s n|≤B := by
  unfold lowCoefficient
  split_ifs with hn
  · exact hcap n (Finset.mem_filter.mp hn).1
  · simpa using hB

theorem remainder_eq_integer (X s L R : ℝ)
    (hpos : ∀n∈support X s, 0<n) (hL : 0≤L) (hR : 0≤R) :
    HarmanDivisorWindow.remainder (lowSupport X s (109/200)) (coefficient X s) L R =
      SingletonMoving.remainder (Finset.Icc 1 ⌊X^(109/200:ℝ)⌋₊)
        (lowCoefficient X s) R (R-L) := by
  rw [HarmanDivisorWindow.remainder_eq_sum]
  change (∑n∈lowSupport X s (109/200), coefficient X s n *
    FrontierSmallBracketSplit.windowKernel L R n) = _
  have he : (∑n∈lowSupport X s (109/200), coefficient X s n *
      FrontierSmallBracketSplit.windowKernel L R n) =
      ∑n∈Finset.Icc 1 ⌊X^(109/200:ℝ)⌋₊, lowCoefficient X s n *
        FrontierSmallBracketSplit.windowKernel L R n := by
    calc
      _ = ∑n∈lowSupport X s (109/200), lowCoefficient X s n *
          FrontierSmallBracketSplit.windowKernel L R n := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [lowCoefficient,ite_eq_left hn]
      _ = _ := Finset.sum_subset (support_subset X s hpos) (by
        intro n _ hn
        simp only [lowCoefficient,ite_eq_right hn,zero_mul])
  rw [he]
  simp only [SingletonMoving.remainder,
    SingletonActualApplication.windowKernel_eq_discrepancy L R hL hR]

theorem moving_remainder_eq (X s Y x : ℝ) (hX : 0<X)
    (hpos : ∀n∈support X s, 0<n) (hY : 0≤Y ∧ Y≤X) (hx : x∈Icc X (2*X)) :
    low X s (109/200) x (x*Y/X) =
      SingletonMoving.remainder (Finset.Icc 1 ⌊X^(109/200:ℝ)⌋₊)
        (lowCoefficient X s) x (x*Y/X) := by
  have hx0 : 0≤x := hX.le.trans hx.1
  have hl : 0≤x-x*Y/X := by
    have hh := (div_le_iff₀ hX).mpr (mul_le_mul_of_nonneg_left hY.2 hx0)
    linarith
  simpa only [low,sub_sub_cancel] using
    remainder_eq_integer X s (x-x*Y/X) x hpos hl hx0

theorem moving_square_integral_eq (X s Y : ℝ) (hX : 0<X)
    (hpos : ∀n∈support X s, 0<n) (hY : 0≤Y ∧ Y≤X) :
    (∫x in Icc X (2*X), low X s (109/200) x (x*Y/X)^2) =
      ∫x in Icc X (2*X), SingletonMoving.remainder
        (Finset.Icc 1 ⌊X^(109/200:ℝ)⌋₊) (lowCoefficient X s) x (x*Y/X)^2 := by
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  dsimp only
  rw [moving_remainder_eq X s Y x hX hpos hY hx]

run_cmd do
  for decl in [``support_subset,``coefficient_cap,``remainder_eq_integer,
      ``moving_remainder_eq,``moving_square_integral_eq] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "COMPLETE PHYSICAL LOW BAND EXACT INTEGER-FLOOR ADAPTER PASSED"

end DirectMovingPhysicalAdapter
