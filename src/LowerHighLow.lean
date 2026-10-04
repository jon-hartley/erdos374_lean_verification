import DirectMovingBound
import DirectMovingEnvelope
import DirectMovingPhysicalAdapter
import PositiveSharpRemainderAnalysisBoxed
import TripleFirstMean

/-! The exact lower-source low physical band, with an independent bound on
its own literal boxed coefficient. No complete-coefficient cancellation is used. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LowerHighLow
open SieveWeightedCutoffs SieveWeightedScalarBudget PositiveSharpPowerWindow
open Erdos374

def support (X s : ℝ) : Finset ℕ :=
  SieveBoxedWindow.support (level X s) s (X^alpha s)

def coefficient (X s : ℝ) (n : ℕ) : ℝ :=
  -SieveBoxedWindow.coefficient (level X s) s (X^alpha s) n

def lowSupport (X s : ℝ) : Finset ℕ :=
  (support X s).filter (fun n => (n:ℝ)≤X^(109/200:ℝ))

def lowRemainder (X s L R : ℝ) : ℝ :=
  HarmanDivisorWindow.remainder (lowSupport X s) (coefficient X s) L R

def zeroCoefficient (X s : ℝ) (n : ℕ) : ℝ :=
  if n∈lowSupport X s then coefficient X s n else 0

theorem support_positive (X s : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀n∈support X s, 0<n :=
  SieveBoxedWindow.support_positive _ _ _
    (PositiveSharpBoxedCount.first_geometry X s hX hs.le hs1).1 hs

theorem support_subset (X s : ℝ) (hpos : ∀n∈support X s, 0<n) :
    lowSupport X s ⊆ Finset.Icc 1 ⌊X^(109/200:ℝ)⌋₊ := by
  intro n hn
  obtain ⟨hn,hbound⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_Icc.mpr ⟨hpos n hn,Nat.le_floor hbound⟩

/-- This cap is a direct consequence of the independent lower boxed-family
bound, uniform in its actual level and prime cutoff. -/
theorem eventually_coefficient_cap (s ε : ℝ) (hs : 0<s) (hs1 : s≤1/1000)
    (hε : 0<ε) :
    ∀ᶠ X:ℝ in atTop, 1<X ∧ ∀n:ℕ, |zeroCoefficient X s n|≤X^ε := by
  filter_upwards [PositiveSharpRemainderAnalysisBoxed.eventually_actual_coefficient_cap s ε hε,
    eventually_gt_atTop (1:ℝ)] with X hc hX
  refine ⟨hX,?_⟩
  intro n
  unfold zeroCoefficient
  split_ifs with hn
  · have hpos := support_positive X s hX hs hs1 n (Finset.mem_filter.mp hn).1
    have hnX : (n:ℝ)≤X^2 := (Finset.mem_filter.mp hn).2.trans (by
      simpa using Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num : (109/200:ℝ)≤2))
    simpa only [coefficient,abs_neg] using
      (hc.2 (level X s) (X^alpha s) n (Nat.ne_of_gt hpos) hnX).1
  · simp only [abs_zero]
    positivity

theorem remainder_eq_integer (X s L R : ℝ)
    (hpos : ∀n∈support X s, 0<n) (hL : 0≤L) (hR : 0≤R) :
    lowRemainder X s L R =
      SingletonMoving.remainder (Finset.Icc 1 ⌊X^(109/200:ℝ)⌋₊)
        (zeroCoefficient X s) R (R-L) := by
  rw [lowRemainder,HarmanDivisorWindow.remainder_eq_sum]
  change (∑n∈lowSupport X s, coefficient X s n *
    FrontierSmallBracketSplit.windowKernel L R n) = _
  have he : (∑n∈lowSupport X s, coefficient X s n *
      FrontierSmallBracketSplit.windowKernel L R n) =
      ∑n∈Finset.Icc 1 ⌊X^(109/200:ℝ)⌋₊, zeroCoefficient X s n *
        FrontierSmallBracketSplit.windowKernel L R n := by
    calc
      _ = ∑n∈lowSupport X s, zeroCoefficient X s n *
          FrontierSmallBracketSplit.windowKernel L R n := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [zeroCoefficient,ite_eq_left hn]
      _ = _ := Finset.sum_subset (support_subset X s hpos) (by
        intro n _ hn
        simp only [zeroCoefficient,ite_eq_right hn,zero_mul])
  rw [he]
  simp only [SingletonMoving.remainder,
    SingletonActualApplication.windowKernel_eq_discrepancy L R hL hR]

theorem moving_square_integral_eq (X s Y : ℝ) (hX : 0<X)
    (hpos : ∀n∈support X s, 0<n) (hY : 0≤Y ∧ Y≤X) :
    (∫x in Icc X (2*X), lowRemainder X s (x-x*Y/X) x ^2) =
      ∫x in Icc X (2*X), SingletonMoving.remainder
        (Finset.Icc 1 ⌊X^(109/200:ℝ)⌋₊) (zeroCoefficient X s) x (x*Y/X)^2 := by
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  have hx0 : 0≤x := hX.le.trans hx.1
  have hl : 0≤x-x*Y/X := by
    have hh := (div_le_iff₀ hX).mpr (mul_le_mul_of_nonneg_left hY.2 hx0)
    linarith
  dsimp only
  rw [remainder_eq_integer X s _ _ hpos hl hx0,sub_sub_cancel]

theorem eventually_square_bound (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X:ℝ in atTop, 1<X ∧
      let Y:=halfWidth X (101/1000)
      (1/X)*(∫x in Icc X (2*X),lowRemainder X s (x-x*Y/X) x ^2)≤
        Y^2*X^(-(1/250:ℝ)) := by
  filter_upwards [DirectMovingEnvelope.eventually_uniform_bound,
    eventually_coefficient_cap s (1/1000) hs hs1 (by norm_num),
    halfWidth_eventually (101/1000) (by norm_num)] with X he hc hhalf
  refine ⟨he.1,?_⟩
  have hXp : 0<X := by linarith [he.1]
  let Q:=⌊X^(109/200:ℝ)⌋₊
  let F:=⌈X^2⌉₊
  let Y:=halfWidth X (101/1000)
  have hQ : 1≤Q := Nat.le_floor (by
    simpa using Real.one_le_rpow he.1.le (by norm_num : (0:ℝ)≤109/200))
  have hQX : (Q:ℝ)≤X^(109/200:ℝ) := Nat.floor_le (Real.rpow_nonneg hXp.le _)
  have hF : 0<F := Nat.one_le_ceil_iff.mpr (sq_pos_of_pos hXp)
  have hYX : 0≤Y ∧ Y≤X := ⟨hhalf.1.le,by have hh:=hhalf.2; linarith⟩
  have hYhalf : Y≤X/2 := by have hh:=hhalf.2; linarith
  have hb := DirectMovingBound.moving_bound Q F (zeroCoefficient X s)
    (X^(1/1000:ℝ)) X Y hQ hF (by positivity) hXp hhalf.1 hYhalf (fun n _ => hc.2 n)
  rw [intervalIntegral.integral_of_le (by linarith : X≤2*X),
    ←integral_Icc_eq_integral_Ioc] at hb
  change (1/X)*(∫x in Icc X (2*X),SingletonMoving.remainder (Finset.Icc 1 Q)
    (zeroCoefficient X s) x (x*Y/X)^2)≤
      (X^(1/1000:ℝ))^2*DirectMovingEnvelope.proposedBound Q F X Y at hb
  change (1/X)*(∫x in Icc X (2*X),lowRemainder X s (x-x*Y/X) x ^2)≤_
  rw [moving_square_integral_eq X s Y hXp (support_positive X s he.1 hs hs1) hYX]
  exact hb.trans (he.2 Q hQ hQX)

theorem eventually_absolute_power (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X:ℝ in atTop, 1<X ∧
      let Y:=halfWidth X (101/1000)
      (1/X)*(∫x in Icc X (2*X),|lowRemainder X s (x-x*Y/X) x|)≤
        Y*X^(-(1/500:ℝ)) := by
  filter_upwards [eventually_square_bound s hs hs1,
    halfWidth_eventually (101/1000) (by norm_num)] with X hb hY
  have hXp : 0<X := by linarith [hb.1]
  let Y:=halfWidth X (101/1000)
  have hYX : Y≤X := by have hh:=hY.2; linarith
  have hsq : (1/X)*(∫x in Icc X (2*X),lowRemainder X s (x-x*Y/X) x ^2)≤
      (Y*X^(-(1/500:ℝ)))^2 := by
    have he : (Y*X^(-(1/500:ℝ)))^2=Y^2*X^(-(1/250:ℝ)) := by
      rw [mul_pow,←Real.rpow_mul_natCast hXp.le]
      norm_num
    rw [he]
    exact hb.2
  have hh := TripleFirstMean.remainder_absolute_mean_le (lowSupport X s) (coefficient X s)
    X Y (Y*X^(-(1/500:ℝ))) hXp hY.1.le hYX
    (mul_pos hY.1 (Real.rpow_pos_of_pos hXp _)) (by
      simpa only [lowRemainder,mul_div_assoc] using hsq)
  refine ⟨hb.1,?_⟩
  simpa only [lowRemainder,mul_div_assoc] using hh

theorem eventually_absolute_log (s : ℝ) (A : ℕ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X:ℝ in atTop, 1<X ∧
      let Y:=halfWidth X (101/1000)
      (1/X)*(∫x in Icc X (2*X),|lowRemainder X s (x-x*Y/X) x|)≤Y/(Real.log X)^A := by
  filter_upwards [eventually_absolute_power s hs hs1,
    PolynomialLogEnvelope.eventually_bound 1 A (1/500) (by norm_num) (by norm_num),
    halfWidth_eventually (101/1000) (by norm_num)] with X hb he hY
  have hXp : 0<X := by linarith [hb.1]
  have hl : 0<Real.log X := Real.log_pos hb.1
  have hlog : (Real.log X)^A≤X^(1/500:ℝ) := by
    apply le_trans _ he.2
    simp only [one_mul]
    exact pow_le_pow_left₀ hl.le (by linarith) A
  have hunit : X^(-(1/500:ℝ))*(Real.log X)^A≤1 := by
    calc
      _ ≤ X^(-(1/500:ℝ))*X^(1/500:ℝ) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = 1 := by rw [←Real.rpow_add hXp]; norm_num
  refine ⟨hb.1,hb.2.trans ?_⟩
  apply (le_div_iff₀ (pow_pos hl A)).mpr
  have hh := mul_le_mul_of_nonneg_left hunit hY.1.le
  nlinarith

run_cmd do
  for decl in [``support,``coefficient,``lowSupport,``lowRemainder,``zeroCoefficient,
      ``support_positive,``support_subset,``eventually_coefficient_cap,``remainder_eq_integer,
      ``moving_square_integral_eq,``eventually_square_bound,``eventually_absolute_power,
      ``eventually_absolute_log] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "LITERAL LOWER SOURCE LOW .545 BAND ALL LOG FIRST MEANS; INDEPENDENT COEFFICIENT CAP"

end LowerHighLow
