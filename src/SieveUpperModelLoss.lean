import SieveUpperBoxWindow
import SieveSmallPrimeFundamental
import SieveFullCutoffTransfer

/-! Exact positive small-bracket excess for the actual upper boxed main term.
The large-family discrepancy is retained explicitly; no analytic estimate of
that discrepancy or of a divisor remainder is asserted here. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
namespace SieveUpperModelLoss
open SieveModelLoss (euler loss)

def outerMass (D s z : ℝ) : ℝ :=
  ∑ t ∈ SieveUpperBoxing.outerFamily D s z, 1/(t.prod : ℝ)

def innerMass (D s z : ℝ) : ℝ :=
  ∑ t ∈ SieveUpperBoxing.innerFamily D s z, 1/(t.prod : ℝ)

def ideal (D s z : ℝ) : ℝ := euler D s*(outerMass D s z-innerMass D s z)

def excess (D s z : ℝ) : ℝ := SieveUpperBoxWindow.mainTerm D s z-ideal D s z

def largeDiscrepancy (D s z : ℝ) : ℝ :=
  outerMass D s z-innerMass D s z-SieveFullCutoffTransfer.upperLarge D s z

theorem outerMass_nonneg (D s z : ℝ) : 0 ≤ outerMass D s z := by
  exact Finset.sum_nonneg (fun t _ => div_nonneg (by norm_num) (Nat.cast_nonneg _))

theorem innerMass_nonneg (D s z : ℝ) : 0 ≤ innerMass D s z := by
  exact Finset.sum_nonneg (fun t _ => div_nonneg (by norm_num) (Nat.cast_nonneg _))

theorem mainTerm_exact (D s z : ℝ) :
    SieveUpperBoxWindow.mainTerm D s z = ideal D s z+
      loss D s true*outerMass D s z+loss D s false*innerMass D s z := by
  change SieveBoxedWindow.smallMass D s true*outerMass D s z-
    SieveBoxedWindow.smallMass D s false*innerMass D s z = _
  rw [SieveModelLoss.small_upper_exact, SieveModelLoss.small_lower_exact, ideal]
  ring

theorem excess_exact (D s z : ℝ) :
    excess D s z = loss D s true*outerMass D s z+loss D s false*innerMass D s z := by
  rw [excess, mainTerm_exact]
  ring

theorem excess_nonneg (D s z : ℝ) : 0 ≤ excess D s z := by
  rw [excess_exact]
  exact add_nonneg
    (mul_nonneg (SieveModelLoss.loss_nonneg D s true) (outerMass_nonneg D s z))
    (mul_nonneg (SieveModelLoss.loss_nonneg D s false) (innerMass_nonneg D s z))

theorem ideal_le_mainTerm (D s z : ℝ) :
    ideal D s z ≤ SieveUpperBoxWindow.mainTerm D s z :=
  sub_nonneg.mp (excess_nonneg D s z)

theorem excess_le_of_relative_loss (D s z δ : ℝ)
    (hsmall : ∀ mode, loss D s mode ≤ δ*euler D s) :
    excess D s z ≤ δ*euler D s*(outerMass D s z+innerMass D s z) := by
  rw [excess_exact, mul_add]
  exact add_le_add
    (mul_le_mul_of_nonneg_right (hsmall true) (outerMass_nonneg D s z))
    (mul_le_mul_of_nonneg_right (hsmall false) (innerMass_nonneg D s z))

theorem excess_le_decay (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) (hsHalf : s ≤ 1/2) :
    excess D s z ≤
      SieveSmallPrimeFundamental.decayConstant*Real.exp (-1/s)*euler D s*
        (outerMass D s z+innerMass D s z) :=
  excess_le_of_relative_loss D s z _
    (fun mode => SieveSmallPrimeFundamental.relative_loss_bound D s mode hD hs hsHalf)

theorem mainTerm_le_fullUpper_add_errors (D s z : ℝ) (hu : D^(s^2) ≤ z) :
    SieveUpperBoxWindow.mainTerm D s z ≤ SieveFullCutoffTransfer.fullUpper D z+
      euler D s*largeDiscrepancy D s z+excess D s z := by
  have h := SieveFullCutoffTransfer.euler_mul_upperLarge_le_fullUpper D s z hu
  change euler D s*SieveFullCutoffTransfer.upperLarge D s z ≤ _ at h
  dsimp [largeDiscrepancy, excess, ideal]
  nlinarith

run_cmd do
  for decl in [``outerMass_nonneg, ``innerMass_nonneg, ``mainTerm_exact,
      ``excess_exact, ``excess_nonneg, ``ideal_le_mainTerm,
      ``excess_le_of_relative_loss, ``excess_le_decay, ``mainTerm_le_fullUpper_add_errors] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL UPPER SMALL-LOSS IDENTITY; LARGE-FAMILY AND DIVISOR ERRORS RETAINED"
end SieveUpperModelLoss
end
