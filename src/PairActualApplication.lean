import PairActualCollection
import SingletonActualApplication

/-! Actual pair natural-floor discrepancies agree with the generic integer-floor
family on the physical moving interval. This is an exact adapter only. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace PairActualApplication

theorem remainder_eq_integer (X s z L R : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hz : z≤X^(SieveWeightedScalarBudget.alpha s))
    (hL : 0≤L) (hR : 0≤R) :
    PairActualCollection.remainder X s z L R =
      SingletonMoving.remainder (Finset.Icc 1 ⌊X^(62/125:ℝ)⌋₊)
        (PairActualCollection.coefficient X s z) R (R-L) := by
  rw [PairActualCollection.remainder_eq_Icc X s z L R hX hs hs1 hz]
  simp only [SingletonMoving.remainder,
    SingletonActualApplication.windowKernel_eq_discrepancy L R hL hR]

theorem moving_remainder_eq (X s z Y x : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hz : z≤X^(SieveWeightedScalarBudget.alpha s))
    (hY : 0≤Y ∧ Y≤X) (hx : x∈Icc X (2*X)) :
    PairActualCollection.remainder X s z (x-x*(Y/X)) x =
      SingletonMoving.remainder (Finset.Icc 1 ⌊X^(62/125:ℝ)⌋₊)
        (PairActualCollection.coefficient X s z) x (x*(Y/X)) := by
  have hXp : 0<X := by linarith
  have hxp : 0≤x := by linarith [hx.1]
  have hlower : 0≤x-x*(Y/X) := by
    have hratio : Y/X≤1 := (div_le_one hXp).mpr hY.2
    have hh := mul_le_mul_of_nonneg_left hratio hxp
    linarith
  simpa only [sub_sub_cancel] using
    remainder_eq_integer X s z (x-x*(Y/X)) x hX hs hs1 hz hlower hxp

theorem moving_square_integral_eq (X s z Y : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hz : z≤X^(SieveWeightedScalarBudget.alpha s))
    (hY : 0≤Y ∧ Y≤X) :
    (∫x in Icc X (2*X),PairActualCollection.remainder X s z (x-x*(Y/X)) x ^2) =
      ∫x in Icc X (2*X),SingletonMoving.remainder (Finset.Icc 1 ⌊X^(62/125:ℝ)⌋₊)
        (PairActualCollection.coefficient X s z) x (x*(Y/X)) ^2 := by
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  dsimp only
  rw [moving_remainder_eq X s z Y x hX hs hs1 hz hY hx]

run_cmd do
  for decl in [``remainder_eq_integer,``moving_remainder_eq,``moving_square_integral_eq] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL PAIR NATURAL-FLOOR TO INTEGER-FLOOR ADAPTER PASSED"

end PairActualApplication
