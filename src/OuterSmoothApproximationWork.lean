import OuterSmoothCoreWork

/-! The full separated remainder admits the explicit continuous cutoff
replacement with an absolute-mean power error, including exterior terms.
The signed coefficients and centered floor kernels are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace OuterSmoothApproximationWork
open LongerTupleEncoding OuterSourceReindexWork LongPairCloseDistinctMeanWork
open OuterSmoothCoreWork OuterSmoothErrorSupportWork OuterSmoothErrorMeanWork
open OuterPairSourceDecompositionWork UpperAfter545Remaining
open LongerTupleHigherMeanWork PositiveSharpPowerWindow

theorem box_error_integrable (X s Y : ℝ) (i j : ℕ) :
    IntegrableOn (fun x => ∑r∈ambient X,
      (atomMultiplier X s i j r*maskError X s (drop r) i j r.1)*
        floorKernel (x-x*(Y/X)) x (index r)) (Icc X (2*X)) :=
  integrable_finsetSum (ambient X) (fun r _ =>
    (SparseFloorMeanWork.kernel_integrable (index r) X Y).const_mul _)

theorem smooth_moving_integrable (X s Y : ℝ) :
    IntegrableOn (fun x => smoothRemainder X s (x-x*(Y/X)) x) (Icc X (2*X)) := by
  unfold smoothRemainder smoothBox
  exact integrable_finsetSum (boxPairs s) (fun ij _ =>
    integrable_finsetSum (ambient X) (fun r _ =>
      (SparseFloorMeanWork.kernel_integrable (index r) X Y).const_mul _))

theorem eventually_smooth_error_power (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop, 2≤X ∧ 1000≤Real.log X ∧ ∀Y : ℝ, 0≤Y → Y≤X/2 →
      (1/X)*(∫x in Icc X (2*X),
        |separatedRemainder X s (x-x*(Y/X)) x-smoothRemainder X s (x-x*(Y/X)) x|) ≤
          Y*X^(-9/50:ℝ) := by
  filter_upwards [eventually_mask_error_mean s,
    PolynomialLogEnvelope.eventually_constant_bound ((boxPairs s).card:ℝ) (1/100)
      (Nat.cast_nonneg _) (by norm_num)] with X hm hc
  refine ⟨hm.1,hm.2.1,?_⟩
  intro Y hY hYX
  have hXp : 0<X := by linarith [hm.1]
  have he (x : ℝ) := remainder_difference X s (x-x*(Y/X)) x hm.1 hs hs1 hm.2.1
  simp_rw [he]
  apply (absolute_sum_mean_le (boxPairs s)
    (fun ij x => ∑r∈ambient X,
      (atomMultiplier X s ij.1 ij.2 r*maskError X s (drop r) ij.1 ij.2 r.1)*
        floorKernel (x-x*(Y/X)) x (index r)) X hXp
    (fun ij _ => box_error_integrable X s Y ij.1 ij.2)).trans
  calc
    _ ≤ ∑_ij∈boxPairs s,Y*X^(-19/100:ℝ) := Finset.sum_le_sum (fun ij hij =>
      hm.2.2 ij hij (atomMultiplier X s ij.1 ij.2)
        (fun r _ => atomMultiplier_abs_le X s ij.1 ij.2 r) Y hY hYX)
    _ = (boxPairs s).card*(Y*X^(-19/100:ℝ)) := by simp
    _ ≤ X^(1/100:ℝ)*(Y*X^(-19/100:ℝ)) := mul_le_mul_of_nonneg_right hc.2 (by positivity)
    _ = Y*X^(-9/50:ℝ) := by
      rw [mul_left_comm,←Real.rpow_add hXp]
      norm_num

theorem eventually_smooth_error_log_unit (s : ℝ) (A : ℕ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop, 2≤X ∧ 1000≤Real.log X ∧
      let Y := halfWidth X (101/1000)
      (1/X)*(∫x in Icc X (2*X),
        |separatedRemainder X s (x-x*(Y/X)) x-smoothRemainder X s (x-x*(Y/X)) x|) ≤
          Y/(Real.log X)^A := by
  filter_upwards [eventually_smooth_error_power s hs hs1,
    PolynomialLogEnvelope.eventually_bound 1 A (9/50) (by norm_num) (by norm_num),
    halfWidth_eventually (101/1000) (by norm_num)] with X hb he hY
  refine ⟨hb.1,hb.2.1,(hb.2.2 _ hY.1.le (by linarith [hY.2])).trans ?_⟩
  have hl : 0<Real.log X := by linarith [hb.2.1]
  have hXp : 0<X := by linarith [hb.1]
  have hlog : (Real.log X)^A ≤ X^(9/50:ℝ) := by
    apply le_trans _ he.2
    simp only [one_mul]
    exact pow_le_pow_left₀ hl.le (by linarith) A
  apply (le_div_iff₀ (pow_pos hl A)).mpr
  have hunit : X^(-9/50:ℝ)*(Real.log X)^A ≤ 1 := by
    calc
      _ ≤ X^(-9/50:ℝ)*X^(9/50:ℝ) := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = 1 := by rw [←Real.rpow_add hXp]; norm_num
  have hh := mul_le_mul_of_nonneg_left hunit hY.1.le
  simpa only [mul_assoc,mul_one] using hh

run_cmd do
  for decl in [``box_error_integrable, ``smooth_moving_integrable,
      ``eventually_smooth_error_power, ``eventually_smooth_error_log_unit] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterSmoothApproximationWork
