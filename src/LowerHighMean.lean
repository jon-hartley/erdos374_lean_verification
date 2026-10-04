import LowerHighLow
import UpperAfter545Remaining
import TripleActualCollectionFirstMean

/-! Every fixed inverse-log absolute first-mean saving for the entire lower
source physical band above X^.545. The upper families and sourceResidualAbs
are not estimated by this module. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LowerHighMean
open SieveWeightedCutoffs SieveWeightedScalarBudget PositiveSharpPowerWindow
open LowerHighLow UpperAfter545Remaining

theorem whole_eq_remainder (X s L R : ℝ) :
    SieveBoxedWindow.sourceRemainder (level X s) s (X^alpha s) L R =
      HarmanDivisorWindow.remainder (support X s) (coefficient X s) L R := by
  simp only [SieveBoxedWindow.sourceRemainder,HarmanDivisorWindow.remainder_eq_sum,
    support,coefficient,neg_mul,Finset.sum_neg_distrib]

theorem whole_eq_low_add_high (X s L R : ℝ) :
    SieveBoxedWindow.sourceRemainder (level X s) s (X^alpha s) L R =
      lowRemainder X s L R+lowerHighRemainder X s L R := by
  rw [whole_eq_remainder]
  simp only [lowRemainder,lowerHighRemainder,HarmanDivisorWindow.remainder_eq_sum]
  change (∑m∈support X s, coefficient X s m *
    (FrontierSmallBracketSplit.windowKernel L R m)) = _
  have hh := Finset.sum_filter_add_sum_filter_not (support X s)
    (fun m:ℕ => (m:ℝ)≤X^(109/200:ℝ))
    (fun m => coefficient X s m * FrontierSmallBracketSplit.windowKernel L R m)
  simpa only [lowSupport,support,coefficient,not_le,FrontierSmallBracketSplit.windowKernel]
    using hh.symm

def absoluteMean (X s Y : ℝ) : ℝ :=
  (1/X)*(∫x in Icc X (2*X),|lowerHighRemainder X s (x-x*Y/X) x|)

theorem absoluteMean_le (X s Y : ℝ) (hX : 0<X) :
    absoluteMean X s Y ≤
      (1/X)*(∫x in Icc X (2*X),
        |SieveBoxedWindow.sourceRemainder (level X s) s (X^alpha s) (x-x*Y/X) x|)+
      (1/X)*(∫x in Icc X (2*X),|lowRemainder X s (x-x*Y/X) x|) := by
  have hwhole : IntegrableOn (fun x =>
      SieveBoxedWindow.sourceRemainder (level X s) s (X^alpha s) (x-x*Y/X) x)
      (Icc X (2*X)) := by
    simpa only [whole_eq_remainder] using
      TailRemainderBand.moving_remainder_integrable (support X s) (coefficient X s) X Y
  have hlow : IntegrableOn (fun x => lowRemainder X s (x-x*Y/X) x) (Icc X (2*X)) :=
    TailRemainderBand.moving_remainder_integrable (lowSupport X s) (coefficient X s) X Y
  have hhigh : IntegrableOn (fun x => lowerHighRemainder X s (x-x*Y/X) x) (Icc X (2*X)) :=
    TailRemainderBand.moving_remainder_integrable _ _ X Y
  have hh := setIntegral_mono_on hhigh.abs (hwhole.abs.add hlow.abs) measurableSet_Icc
    (fun x (_hx:x∈Icc X (2*X)) => by
      have he := whole_eq_low_add_high X s (x-x*Y/X) x
      have hsub : lowerHighRemainder X s (x-x*Y/X) x =
          SieveBoxedWindow.sourceRemainder (level X s) s (X^alpha s) (x-x*Y/X) x-
            lowRemainder X s (x-x*Y/X) x := by linarith
      change |lowerHighRemainder X s (x-x*Y/X) x|≤_
      rw [hsub]
      exact abs_sub _ _)
  simp only [Pi.add_apply] at hh
  rw [integral_add hwhole.abs hlow.abs] at hh
  simpa only [absoluteMean,mul_add] using
    mul_le_mul_of_nonneg_left hh (show 0≤1/X by positivity)

theorem eventually_absolute_log (s : ℝ) (A : ℕ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X:ℝ in atTop, 1<X ∧
      absoluteMean X s (halfWidth X (101/1000))≤
        halfWidth X (101/1000)/(Real.log X)^A := by
  filter_upwards [TripleActualCollectionFirstMean.eventually_log_bound s hs hs1 (A+1),
    LowerHighLow.eventually_absolute_log s (A+1) hs hs1,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2:ℝ))] with X hw hl hlog
  have hXp : 0<X := by linarith [hw.1]
  have hLp : 0<Real.log X := by linarith
  let Y:=halfWidth X (101/1000)
  have hY : 0≤Y := by dsimp [Y,halfWidth]; positivity
  have hwhole : (1/X)*(∫x in Icc X (2*X),
      |SieveBoxedWindow.sourceRemainder (level X s) s (X^alpha s) (x-x*Y/X) x|)≤
        Y/(Real.log X)^(A+1) := by
    simpa only [mul_div_assoc] using hw.2 (X^alpha s) le_rfl
  have hlow : (1/X)*(∫x in Icc X (2*X),|lowRemainder X s (x-x*Y/X) x|)≤
      Y/(Real.log X)^(A+1) := hl.2
  have hden : 2*(Real.log X)^A≤(Real.log X)^(A+1) := by
    rw [pow_succ]
    nlinarith [pow_nonneg hLp.le A]
  have hinv : 2/(Real.log X)^(A+1)≤1/(Real.log X)^A := by
    apply (div_le_div_iff₀ (pow_pos hLp _) (pow_pos hLp _)).mpr
    simpa only [one_mul] using hden
  refine ⟨hw.1,?_⟩
  calc
    absoluteMean X s Y ≤ _ := absoluteMean_le X s Y hXp
    _ ≤ Y/(Real.log X)^(A+1)+Y/(Real.log X)^(A+1) := add_le_add hwhole hlow
    _ = Y*(2/(Real.log X)^(A+1)) := by ring
    _ ≤ Y*(1/(Real.log X)^A) := mul_le_mul_of_nonneg_left hinv hY
    _ = Y/(Real.log X)^A := by ring

run_cmd do
  for decl in [``whole_eq_remainder,``whole_eq_low_add_high,``absoluteMean,
      ``absoluteMean_le,``eventually_absolute_log] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "ENTIRE LOWER SOURCE HIGH PHYSICAL BAND ABOVE .545 HAS EVERY FIXED LOG FIRST-MEAN SAVING"

end LowerHighMean
