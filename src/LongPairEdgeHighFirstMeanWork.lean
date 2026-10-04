import LongPairEdgeHighProfileMeanWork
import TripleFirstMean
import PositiveSharpPowerWindow

/-! Exact collected high-edge profiles, regularity, and all fixed logarithmic
absolute first means. No fluctuation estimate is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LongPairEdgeHighFirstMeanWork
open LongerTupleActualProfiles LongerTupleCollection LongPairProfilesWork
open LongPairEdgeHighProfileMeanWork UpperAfter545Remaining PositiveSharpPowerWindow

def profileSource (X s : ℝ) (second : Bool) (js : List ℕ) : Finset LongerTupleEncoding.Representation :=
  (pairSource X s (PositiveSharpBoxedCount.largePrimes X)
    (SieveWeightedCutoffs.cutoffThree X s) second js).filter
      (fun r => (ShortPairSplitWork.prime second r:ℝ)≤X^(229/1000:ℝ) ∧
        X^(26/35:ℝ)<(LongerTupleEncoding.index r:ℝ))

def divisorSupport (X s : ℝ) (second : Bool) (js : List ℕ) : Finset ℕ :=
  support (profileSource X s second js) LongerTupleEncoding.index

def divisorCoefficient (X s : ℝ) (second : Bool) (js : List ℕ) (m : ℕ) : ℝ :=
  (coefficient (profileSource X s second js) LongerTupleEncoding.index
    (originalWeight X s true) m).re

theorem profile_eq_remainder (X s : ℝ) (second : Bool) (js : List ℕ) (L R : ℝ) :
    (edgeHighKernel X s second js L R).re =
      HarmanDivisorWindow.remainder (divisorSupport X s second js)
        (divisorCoefficient X s second js) L R := by
  have he : edgeHighKernel X s second js L R =
      ∑ r∈profileSource X s second js,
        originalWeight X s true r*(floorKernel L R (LongerTupleEncoding.index r):ℂ) := by
    simp only [edgeHighKernel,profileSource,Finset.sum_filter]
  have hh := congrArg Complex.re (he.trans
    (grouped_sum (profileSource X s second js) LongerTupleEncoding.index
      (originalWeight X s true) (fun m => (floorKernel L R m:ℂ))).symm)
  rw [HarmanDivisorWindow.remainder_eq_sum]
  simpa only [divisorSupport,divisorCoefficient,floorKernel,Complex.re_sum,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] using hh

theorem moving_integrable (X s Y : ℝ) (second : Bool) (js : List ℕ) :
    IntegrableOn (fun x => (edgeHighKernel X s second js (x-x*(Y/X)) x).re)
      (Icc X (2*X)) := by
  simp_rw [profile_eq_remainder]
  simpa only [mul_div_assoc] using TailRemainderBand.moving_remainder_integrable
    (divisorSupport X s second js) (divisorCoefficient X s second js) X Y

theorem eventually_pair_absolute_power (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1/1000)
    :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, 1 < X ∧ 1000 ≤ Real.log X ∧
      ∀ (second : Bool) (js : List ℕ), js.length = 2 →
        let Y : ℝ := halfWidth X (101/1000)
        (1/X)*(∫ x in Icc X (2*X),
          |(edgeHighKernel X s second js (x-x*(Y/X)) x).re|) ≤ Y*X^(-c) := by
  obtain ⟨c,hc,hmean⟩ := eventually_edgeHigh_square s hs hs1
  refine ⟨c/2,by positivity,?_⟩
  filter_upwards [hmean, halfWidth_eventually (101/1000) (by norm_num)] with X hm hY
  refine ⟨hm.1,hm.2.1,?_⟩
  intro second js hlen
  let P := PositiveSharpBoxedCount.largePrimes X
  let z := SieveWeightedCutoffs.cutoffThree X s
  dsimp only
  have hXp : 0 < X := by linarith [hm.1]
  let Y := halfWidth X (101/1000)
  have hYX : Y ≤ X := by have hh := hY.2; linarith
  have hsq : (1/X)*(∫ x in Icc X (2*X),
      (edgeHighKernel X s second js (x-x*(Y/X)) x).re^2) ≤
      (Y*X^(-(c/2)))^2 := by
    have he : (Y*X^(-(c/2)))^2 = Y^2*X^(-c) := by
      rw [mul_pow, ←Real.rpow_mul_natCast hXp.le]
      congr 2
      norm_num
    rw [he]
    exact hm.2.2 second js hlen
  simp_rw [profile_eq_remainder] at hsq ⊢
  exact TripleFirstMean.remainder_absolute_mean_le _ _ X Y
    (Y*X^(-(c/2))) hXp hY.1.le hYX
    (mul_pos hY.1 (Real.rpow_pos_of_pos hXp _)) hsq

theorem eventually_pair_absolute_log (s : ℝ) (A : ℕ)
    (hs : 0 < s) (hs1 : s ≤ 1/1000) :
    ∀ᶠ X : ℝ in atTop, 1 < X ∧ 1000 ≤ Real.log X ∧
      ∀ (second : Bool) (js : List ℕ), js.length = 2 →
        let Y : ℝ := halfWidth X (101/1000)
        (1/X)*(∫ x in Icc X (2*X),
          |(edgeHighKernel X s second js (x-x*(Y/X)) x).re|) ≤
          Y/(Real.log X)^A := by
  obtain ⟨c,hc,hpower⟩ := eventually_pair_absolute_power s hs hs1
  filter_upwards [hpower, PolynomialLogEnvelope.eventually_bound 1 A c (by norm_num) hc,
    halfWidth_eventually (101/1000) (by norm_num)] with X hb he hY
  refine ⟨hb.1,hb.2.1,?_⟩
  intro second js hlen
  let P := PositiveSharpBoxedCount.largePrimes X
  let z := SieveWeightedCutoffs.cutoffThree X s
  dsimp only
  have hXp : 0 < X := by linarith [hb.1]
  have hl : 0 < Real.log X := Real.log_pos hb.1
  have hlog : (Real.log X)^A ≤ X^c := by
    apply le_trans _ he.2
    simp only [one_mul]
    exact pow_le_pow_left₀ hl.le (by linarith) A
  have hunit : X^(-c)*(Real.log X)^A ≤ 1 := by
    calc
      _ ≤ X^(-c)*X^c := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = 1 := by rw [←Real.rpow_add hXp]; simp
  apply (hb.2.2 second js hlen).trans
  apply (le_div_iff₀ (pow_pos hl A)).mpr
  have hh := mul_le_mul_of_nonneg_left hunit hY.1.le
  nlinarith

#print axioms eventually_pair_absolute_log
run_cmd do
  for decl in [``profile_eq_remainder, ``moving_integrable, ``eventually_pair_absolute_power,
      ``eventually_pair_absolute_log] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "LITERAL HIGH EDGE PROFILE EVERY FIXED LOG FIRST MEAN PASSED"

end LongPairEdgeHighFirstMeanWork
