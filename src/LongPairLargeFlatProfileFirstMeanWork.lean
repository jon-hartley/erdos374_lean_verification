import LongPairLargeFlatProfileMeanWork
import TripleFirstMean
import PositiveSharpPowerWindow

/-! First means for the exact capped large-band long-pair profiles. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LongPairLargeFlatProfileFirstMeanWork
open LongerTupleActualProfiles LongerTupleCollection LongPairProfilesWork
open LongPairLargeFlatProfileMeanWork UpperAfter545Remaining PositiveSharpPowerWindow

def divisorSupport (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) : Finset ℕ :=
  support (pairSource X s P z second js) LongerTupleEncoding.index

def divisorCoefficient (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (U : ℝ) (m : ℕ) : ℝ :=
  if (m:ℝ)≤U then
    (coefficient (pairSource X s P z second js) LongerTupleEncoding.index
      (originalWeight X s true) m).re else 0

theorem profile_eq_remainder (X s : ℝ) (P : Finset ℕ) (z : ℝ → ℝ)
    (second : Bool) (js : List ℕ) (U L R : ℝ) :
    cappedKernel X s P z second js U (floorKernel L R) =
      HarmanDivisorWindow.remainder (divisorSupport X s P z second js)
        (divisorCoefficient X s P z second js U) L R := by
  unfold cappedKernel
  have hh := congrArg Complex.re
    ((pairKernel_eq_source X s P z second js
      (fun m => if (m:ℝ)≤U then floorKernel L R m else 0)).trans
      (grouped_sum (pairSource X s P z second js) LongerTupleEncoding.index
        (originalWeight X s true)
        (fun m => Complex.ofReal (if (m:ℝ)≤U then floorKernel L R m else 0))).symm)
  rw [HarmanDivisorWindow.remainder_eq_sum]
  simp only [Complex.ofReal_re,Complex.re_sum,Complex.mul_re,Complex.ofReal_im,
    mul_zero,sub_zero] at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : (m:ℝ)≤U <;>
    simp only [divisorCoefficient,hm,ite_true,ite_false,mul_zero,zero_mul,floorKernel]

theorem eventually_pair_absolute_power (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1/1000)
    :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, 1 < X ∧ 1000 ≤ Real.log X ∧
      ∀ (second : Bool) (js : List ℕ), js.length = 2 →
        let Y : ℝ := halfWidth X (101/1000)
        (1/X)*(∫ x in Icc X (2*X),
          |cappedKernel X s (PositiveSharpBoxedCount.largePrimes X)
            (SieveWeightedCutoffs.cutoffThree X s) second js (X^(26/35:ℝ)) (floorKernel (x-x*(Y/X)) x)|) ≤ Y*X^(-c) := by
  obtain ⟨c,hc,hmean⟩ := eventually_capped_square s hs hs1
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
      cappedKernel X s (PositiveSharpBoxedCount.largePrimes X)
            (SieveWeightedCutoffs.cutoffThree X s) second js (X^(26/35:ℝ)) (floorKernel (x-x*(Y/X)) x)^2) ≤
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
          |cappedKernel X s (PositiveSharpBoxedCount.largePrimes X)
            (SieveWeightedCutoffs.cutoffThree X s) second js (X^(26/35:ℝ)) (floorKernel (x-x*(Y/X)) x)|) ≤
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
  for decl in [``profile_eq_remainder, ``eventually_pair_absolute_power,
      ``eventually_pair_absolute_log] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "LITERAL CAPPED LARGE-BAND LONG PAIR PROFILE EVERY FIXED LOG FIRST MEAN PASSED"

end LongPairLargeFlatProfileFirstMeanWork
