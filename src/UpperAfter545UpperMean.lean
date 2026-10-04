import UpperAfter545Remaining
import TailRemainderBand

/-! First-mean reduction for the actual remaining upper kernels.  The lower
absolute mean and the remaining-upper negative mean are explicit, and no
estimate for either is hidden in an integrability assumption. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter MeasureTheory Set

namespace UpperAfter545UpperMean
open UpperAfter545Remaining

def lowerHighAbsoluteMean (X s Y : ℝ) : ℝ :=
  (∫ x in Icc X (2*X), |lowerHighRemainder X s (x-x*Y/X) x|)/X

def remainingUpperNegativeMean (X s Y : ℝ) : ℝ :=
  (∫ x in Icc X (2*X), max (-upperRemainingRemainder X s (x-x*Y/X) x) 0)/X

theorem lower_high_integrable (X s Y : ℝ) :
    IntegrableOn (fun x => lowerHighRemainder X s (x-x*Y/X) x) (Icc X (2*X)) :=
  TailRemainderBand.moving_remainder_integrable _ _ X Y

theorem lower_high_absolute_integrable (X s Y : ℝ) :
    IntegrableOn (fun x => |lowerHighRemainder X s (x-x*Y/X) x|) (Icc X (2*X)) :=
  (lower_high_integrable X s Y).abs

/-- Compact integrability follows from the exact difference of two literal
finite divisor remainders; it requires no size bound on the moving width. -/
theorem remaining_upper_integrable (X s Y : ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) :
    IntegrableOn (fun x => upperRemainingRemainder X s (x-x*Y/X) x) (Icc X (2*X)) := by
  have he : (fun x => upperRemainingRemainder X s (x-x*Y/X) x) =
      (fun x => MomentSmallRemainder.high X s (109/200) x (x*Y/X) -
        lowerHighRemainder X s (x-x*Y/X) x) := by
    funext x
    have hh := complete_high_eq_lower_add_upper X s x (x*Y/X) hX hs hs1 hlog
    linarith
  rw [he]
  exact (TailRemainderBand.high_integrable X s (109/200) Y).sub (lower_high_integrable X s Y)

theorem remaining_upper_negative_integrable (X s Y : ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) :
    IntegrableOn (fun x => max (-upperRemainingRemainder X s (x-x*Y/X) x) 0)
      (Icc X (2*X)) :=
  (remaining_upper_integrable X s Y hX hs hs1 hlog).neg_part

theorem highNegativeMean_le_lower_add_upper (X s Y : ℝ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X) :
    TailRemainderBand.highNegativeMean X s (109/200) Y ≤
      lowerHighAbsoluteMean X s Y + remainingUpperNegativeMean X s Y := by
  have hl := lower_high_absolute_integrable X s Y
  have hu := remaining_upper_negative_integrable X s Y hX hs hs1 hlog
  have hb := setIntegral_mono_on
    (TailRemainderBand.high_integrable X s (109/200) Y).neg_part
    (hl.add hu) measurableSet_Icc (fun x (_hx : x ∈ Icc X (2*X)) =>
      negative_part_le X s x (x*Y/X) hX hs hs1 hlog)
  simp only [Pi.add_apply] at hb
  rw [integral_add hl hu] at hb
  unfold TailRemainderBand.highNegativeMean lowerHighAbsoluteMean remainingUpperNegativeMean
  rw [←add_div]
  exact div_le_div_of_nonneg_right hb (by linarith)

theorem eventually_highNegativeMean_le_lower_add_upper (s : ℝ)
    (hs : 0 < s) (hs1 : s ≤ 1/1000) :
    ∀ᶠ X : ℝ in atTop, ∀ Y : ℝ,
      TailRemainderBand.highNegativeMean X s (109/200) Y ≤
        lowerHighAbsoluteMean X s Y + remainingUpperNegativeMean X s Y := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1000)] with X hX hlog
  exact fun Y => highNegativeMean_le_lower_add_upper X s Y hX hs hs1 hlog

/-- An explicit conditional combination rule. In particular the remaining
upper logarithmic mean estimate stays a stated analytic hypothesis. -/
theorem eventually_highNegativeMean_of_bounds (s C_lower C_upper : ℝ) (A : ℕ)
    (Y : ℝ → ℝ) (hs : 0 < s) (hs1 : s ≤ 1/1000)
    (hlower : ∀ᶠ X : ℝ in atTop,
      lowerHighAbsoluteMean X s (Y X) ≤ C_lower * Y X / (Real.log X)^A)
    (hupper : ∀ᶠ X : ℝ in atTop,
      remainingUpperNegativeMean X s (Y X) ≤ C_upper * Y X / (Real.log X)^A) :
    ∀ᶠ X : ℝ in atTop,
      TailRemainderBand.highNegativeMean X s (109/200) (Y X) ≤
        (C_lower+C_upper) * Y X / (Real.log X)^A := by
  filter_upwards [eventually_highNegativeMean_le_lower_add_upper s hs hs1,
    hlower, hupper] with X hr hl hu
  calc
    _ ≤ lowerHighAbsoluteMean X s (Y X) + remainingUpperNegativeMean X s (Y X) := hr (Y X)
    _ ≤ C_lower * Y X / (Real.log X)^A + C_upper * Y X / (Real.log X)^A := add_le_add hl hu
    _ = _ := by ring

run_cmd do
  for decl in [``lower_high_integrable, ``lower_high_absolute_integrable,
      ``remaining_upper_integrable, ``remaining_upper_negative_integrable,
      ``highNegativeMean_le_lower_add_upper, ``eventually_highNegativeMean_le_lower_add_upper,
      ``eventually_highNegativeMean_of_bounds] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL REMAINING-UPPER FIRST-MEAN REDUCTION PASSED; UPPER ESTIMATE EXPLICIT"

end UpperAfter545UpperMean
