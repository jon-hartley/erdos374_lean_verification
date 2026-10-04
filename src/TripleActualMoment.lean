import TripleDyadicMeanSquare
import TripleActualGeometryBounds

/-! Every actual remaining outer profile satisfies the flat-product estimate.
The upper small weights, unit divisor and repeated prime tuples are literal
inputs to the exact collection; no analytic premise remains in this theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace TripleActualMoment
open TripleActualGrouping TripleActualGeometry

theorem eventually_profile_bound (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1/1000) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, 1 < X ∧
      ∀ (Y z : ℝ) (a : TailSieveCovered.Index),
        a ∈ PairActualResidual.family X s →
        z ≤ X ^ (SieveWeightedScalarBudget.alpha s) →
        X ^ (1009/10000 : ℝ) ≤ Y → Y ≤ X/2 →
        (1/X) * (∫ x in Icc X (2*X),
          TripleActualGrouping.remainder X s z true a.2.1 a.2.2
            (x-x*(Y/X)) x ^ 2) ≤ Y^2 * X^(-c) := by
  obtain ⟨c,hc,δ,hδ,hd⟩ := TripleDyadicMeanSquare.eventually_bound
  refine ⟨c,hc,?_⟩
  filter_upwards [hd, TripleActualGrouping.eventually_pair_coefficient_cap 2 δ hδ,
    eventually_gt_atTop (1 : ℝ)] with X hd hcap hX
  refine ⟨hX,?_⟩
  intro Y z a ha hz hY hYhalf
  have hprime := prime_support_bounds X s z hX hs hs1 hz a ha
  have hpair := pair_support_bounds X s z hX hs hs1 hz a ha
  have hlen := (PairActualResidual.remaining_cases X s hX hs hs1 a ha).2.1
  apply hd.2 (primeSupport X s z a.2.2) (pairSupport X s z a.2.1)
    (fun _ => 1) (pairCoefficient X s z true a.2.1) Y
  · exact fun n hn => (hprime n hn).1
  · exact fun n hn => (hpair n hn).1
  · exact fun n hn => (hprime n hn).2.2
  · exact fun n hn => (hpair n hn).2.2
  · intro n hn
    simpa only [show (228/1000 : ℝ) = 57/250 by norm_num] using (hprime n hn).2.1.le
  · intro n hn
    simpa only [show (456/1000 : ℝ) = 57/125 by norm_num] using (hpair n hn).2.1.le
  · intro m hm n hn
    simpa only [Nat.cast_mul] using (cross_product_lt X s z hX hs hs1 hz a ha m hm n hn).le
  · intro n _
    simpa only [abs_one] using Real.one_le_rpow hX.le hδ.le
  · intro n hn
    have hp := hpair n hn
    exact hcap.2 s z true a.2.1 n hlen.le (by omega)
      (by nlinarith [hp.2.2])
  · exact hY
  · exact hYhalf

run_cmd do
  for ax in (← Lean.collectAxioms ``eventually_profile_bound) do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "EVERY ACTUAL LOW-D OUTER TRIPLE PROFILE HAS M2 POWER SAVING"

end TripleActualMoment
