import DirectMovingTail
import PairFourierApproximation

/-! Summation and scaling of the anchored residual for the actual moving
hard-projection error. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set intervalIntegral
open scoped Real ENNReal BigOperators

namespace DirectMovingTailAggregate

def term (n F : ℕ) (x : ℝ) : ℂ :=
  if hn : 0<n then DirectMovingTail.residual n hn F x else 0

def aggregate (Q : ℕ) (a : ℕ→ℝ) (F : ℕ) (x : ℝ) : ℂ :=
  ∑n∈Finset.Icc 1 Q, (a n:ℂ)*term n F x

theorem term_memLp (n F : ℕ) (L R : ℝ) (p : ℝ≥0∞) :
    MemLp (term n F) p (volume.restrict (Ioc L R)) := by
  unfold term
  by_cases hn : 0<n
  · simpa only [dite_eq_left hn] using DirectMovingTail.residual_memLp n hn F L R p
  · simp only [dite_eq_right hn]
    exact MemLp.zero'

theorem term_measurable (n F : ℕ) : Measurable (term n F) := by
  unfold term
  by_cases hn : 0<n
  · simpa only [dite_eq_left hn] using DirectMovingTail.residual_measurable n hn F
  · simp only [dite_eq_right hn]
    exact measurable_const

theorem aggregate_measurable (Q : ℕ) (a : ℕ→ℝ) (F : ℕ) :
    Measurable (aggregate Q a F) := by
  exact Finset.measurable_sum _ (fun n _ => measurable_const.mul (term_measurable n F))

theorem aggregate_memLp (Q : ℕ) (a : ℕ→ℝ) (F : ℕ) (L R : ℝ) (p : ℝ≥0∞) :
    MemLp (aggregate Q a F) p (volume.restrict (Ioc L R)) := by
  exact memLp_finsetSum _ (fun n _ => (term_memLp n F L R p).const_mul (a n:ℂ))

theorem term_square_integrable (n F : ℕ) (L R : ℝ) :
    IntervalIntegrable (fun x => ‖term n F x‖^2) volume L R := by
  constructor <;> exact (term_memLp n F _ _ 2).integrable_norm_pow (by norm_num)

theorem square_integrable (Q : ℕ) (a : ℕ→ℝ) (F : ℕ) (L R : ℝ) :
    IntervalIntegrable (fun x => ‖aggregate Q a F x‖^2) volume L R := by
  constructor <;> exact (aggregate_memLp Q a F _ _ 2).integrable_norm_pow (by norm_num)

theorem pointwise_le (Q : ℕ) (a : ℕ→ℝ) (F : ℕ) (B x : ℝ)
    (ha : ∀n∈Finset.Icc 1 Q, |a n|≤B) :
    ‖aggregate Q a F x‖^2 ≤ (Q:ℝ)*B^2*(∑n∈Finset.Icc 1 Q, ‖term n F x‖^2) := by
  have hc : (Finset.Icc 1 Q).card=Q := by simp
  unfold aggregate
  calc
    _ ≤ (∑n∈Finset.Icc 1 Q, ‖(a n:ℂ)*term n F x‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ ((Finset.Icc 1 Q).card:ℝ)*(∑n∈Finset.Icc 1 Q, ‖(a n:ℂ)*term n F x‖^2) :=
      sq_sum_le_card_mul_sum_sq
    _ ≤ (Q:ℝ)*(∑n∈Finset.Icc 1 Q, B^2*‖term n F x‖^2) := by
      rw [hc]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg Q)
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (ha n hn) 2)
        (sq_nonneg _)
    _ = _ := by rw [←Finset.mul_sum]; ring

theorem integral_bound (Q : ℕ) (a : ℕ→ℝ) (F : ℕ) (hF : 0<F)
    (B t T : ℝ) (hT : 0≤T) (ha : ∀n∈Finset.Icc 1 Q, |a n|≤B) :
    (∫x in t..t+T, ‖aggregate Q a F x‖^2) ≤
      (4*B^2*(Q:ℝ)/F)*(T*SingletonHarmonic.harmonicSum Q+Q) := by
  have his : IntervalIntegrable (fun x => ∑n∈Finset.Icc 1 Q, ‖term n F x‖^2)
      volume t (t+T) := by
    constructor <;> exact MeasureTheory.integrable_finsetSum _
      (fun n _ => (term_memLp n F _ _ 2).integrable_norm_pow (by norm_num))
  calc
    _ ≤ ∫x in t..t+T, (Q:ℝ)*B^2*(∑n∈Finset.Icc 1 Q, ‖term n F x‖^2) := by
      apply intervalIntegral.integral_mono_on (by linarith)
        (square_integrable Q a F t (t+T)) (his.const_mul _)
      intro x _
      exact pointwise_le Q a F B x ha
    _ = (Q:ℝ)*B^2*(∑n∈Finset.Icc 1 Q, ∫x in t..t+T, ‖term n F x‖^2) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
      intro n _
      exact term_square_integrable n F t (t+T)
    _ ≤ (Q:ℝ)*B^2*(∑n∈Finset.Icc 1 Q, (4/(F:ℝ))*(T/n+1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : 0<n := by have := (Finset.mem_Icc.mp hn).1; omega
      simp only [term, dite_eq_left hn0]
      exact DirectMovingTail.interval_bound n hn0 F hF t T hT
    _ = _ := by
      simp only [←Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
        nsmul_eq_mul, mul_one, Nat.card_Icc, Nat.add_sub_cancel,
        div_eq_mul_inv, ←Finset.mul_sum, SingletonHarmonic.harmonicSum, one_mul]
      ring

theorem actual_error_eq (Q : ℕ) (a : ℕ→ℝ) (F : ℕ) (h x : ℝ) :
    PairProjectionEnergy.remainder Q a h x - PairFourierApproximation.polynomial Q a h F x =
      aggregate Q a F x - aggregate Q a F (x-h) := by
  rw [PairFourierApproximation.difference_eq_sum]
  unfold aggregate
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : 0<n := by have := (Finset.mem_Icc.mp hn).1; omega
  rw [PairFourierApproximation.singleError_pos n hn0,
    DirectMovingTail.singleError_eq_difference]
  simp only [term, dite_eq_left hn0]
  ring

theorem scaled_square_integrable (Q : ℕ) (a : ℕ→ℝ) (F : ℕ)
    (α L R : ℝ) (hα : α≠0) :
    IntervalIntegrable (fun x => ‖aggregate Q a F (α*x)‖^2) volume L R := by
  have hi := (square_integrable Q a F (α*L) (α*R)).comp_mul_left (c:=α)
  simpa only [mul_div_cancel_left₀ L hα, mul_div_cancel_left₀ R hα] using hi

theorem norm_sub_square_le (z w : ℂ) : ‖z-w‖^2 ≤ 2*‖z‖^2+2*‖w‖^2 := by
  have hh := pow_le_pow_left₀ (norm_nonneg (z-w)) (norm_sub_le z w) 2
  nlinarith [sq_nonneg (‖z‖-‖w‖)]

theorem difference_square_integrable (Q : ℕ) (a : ℕ→ℝ) (F : ℕ)
    (α L R : ℝ) (hα : α≠0) :
    IntervalIntegrable (fun x => ‖aggregate Q a F x-aggregate Q a F (α*x)‖^2)
      volume L R := by
  have h1 := square_integrable Q a F L R
  have h2 := scaled_square_integrable Q a F α L R hα
  have hm : Measurable (fun x => ‖aggregate Q a F x-aggregate Q a F (α*x)‖^2) :=
    ((aggregate_measurable Q a F).sub ((aggregate_measurable Q a F).comp
      (measurable_const.mul measurable_id))).norm.pow_const 2
  have hb (x : ℝ) : ‖‖aggregate Q a F x-aggregate Q a F (α*x)‖^2‖ ≤
      2*‖aggregate Q a F x‖^2+2*‖aggregate Q a F (α*x)‖^2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact norm_sub_square_le _ _
  constructor
  · exact ((h1.1.const_mul 2).add (h2.1.const_mul 2)).mono'
      hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  · exact ((h1.2.const_mul 2).add (h2.2.const_mul 2)).mono'
      hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)

theorem difference_mean_square_bound (Q : ℕ) (a : ℕ→ℝ) (F : ℕ) (hF : 0<F)
    (B X α : ℝ) (hX : 0<X) (hα : 1/2≤α)
    (ha : ∀n∈Finset.Icc 1 Q, |a n|≤B) :
    (1/X)*(∫x in X..2*X, ‖aggregate Q a F x-aggregate Q a F (α*x)‖^2) ≤
      16*B^2*(Q:ℝ)*SingletonHarmonic.harmonicSum Q/F +
        24*B^2*(Q:ℝ)^2/((F:ℝ)*X) := by
  let A : ℝ := 4*B^2*(Q:ℝ)/F
  let J := SingletonHarmonic.harmonicSum Q
  have hα0 : 0<α := by linarith
  have hF0 : (F:ℝ)≠0 := by exact_mod_cast hF.ne'
  have hA : 0≤A := by dsimp [A]; positivity
  have hbase : (∫x in X..2*X, ‖aggregate Q a F x‖^2) ≤ A*(X*J+Q) := by
    simpa only [←two_mul] using integral_bound Q a F hF B X X hX.le ha
  have hscaled : (∫x in X..2*X, ‖aggregate Q a F (α*x)‖^2) ≤ A*(X*J+2*Q) := by
    rw [intervalIntegral.integral_comp_mul_left
      (fun x : ℝ => ‖aggregate Q a F x‖^2) hα0.ne', smul_eq_mul]
    have hb := integral_bound Q a F hF B (α*X) (α*X) (mul_nonneg hα0.le hX.le) ha
    rw [show α*X+α*X=α*(2*X) by ring] at hb
    apply (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hα0.le)).trans
    have hq : (Q:ℝ)/α≤2*(Q:ℝ) := by
      apply (div_le_iff₀ hα0).mpr
      nlinarith [mul_nonneg (Nat.cast_nonneg Q) (show 0≤2*α-1 by linarith)]
    calc
      _ = A*(X*J+(Q:ℝ)/α) := by dsimp [A,J]; field_simp
      _ ≤ A*(X*J+2*Q) := mul_le_mul_of_nonneg_left (add_le_add le_rfl hq) hA
  have h1 := square_integrable Q a F X (2*X)
  have h2 := scaled_square_integrable Q a F α X (2*X) hα0.ne'
  have hi := intervalIntegral.integral_mono_on (by linarith : X≤2*X)
    (difference_square_integrable Q a F α X (2*X) hα0.ne')
    ((h1.const_mul 2).add (h2.const_mul 2))
    (fun x (_hx : x∈Icc X (2*X)) => norm_sub_square_le
      (aggregate Q a F x) (aggregate Q a F (α*x)))
  change (∫x in X..2*X, ‖aggregate Q a F x-aggregate Q a F (α*x)‖^2) ≤
    ∫x in X..2*X, 2*‖aggregate Q a F x‖^2+2*‖aggregate Q a F (α*x)‖^2 at hi
  rw [intervalIntegral.integral_add
    (f:=fun x => 2*‖aggregate Q a F x‖^2)
    (g:=fun x => 2*‖aggregate Q a F (α*x)‖^2) (h1.const_mul 2) (h2.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  calc
    _ ≤ (1/X)*(2*(A*(X*J+Q))+2*(A*(X*J+2*Q))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ = _ := by dsimp [A,J]; field_simp; ring

theorem moving_error_square_integrable (Q F : ℕ) (a : ℕ→ℝ)
    (X H : ℝ) (hX : 0<X) (hH : H≤X/2) :
    IntervalIntegrable (fun x =>
      ‖PairProjectionEnergy.remainder Q a (x*H/X) x -
        PairFourierApproximation.polynomial Q a (x*H/X) F x‖^2) volume X (2*X) := by
  have hα : 0<1-H/X := by
    have hh : H/X≤1/2 := (div_le_iff₀ hX).mpr (by linarith)
    linarith
  have he (x : ℝ) : x-x*H/X=(1-H/X)*x := by ring
  simpa only [actual_error_eq, he] using
    difference_square_integrable Q a F (1-H/X) X (2*X) hα.ne'

theorem moving_error_bound (Q F : ℕ) (a : ℕ→ℝ) (B X H : ℝ)
    (hF : 0<F) (_hB : 0≤B) (hX : 0<X) (hH : H≤X/2)
    (ha : ∀n∈Finset.Icc 1 Q, |a n|≤B) :
    (1/X)*(∫x in X..2*X,
      ‖PairProjectionEnergy.remainder Q a (x*H/X) x -
        PairFourierApproximation.polynomial Q a (x*H/X) F x‖^2) ≤
      16*B^2*(Q:ℝ)*SingletonHarmonic.harmonicSum Q/F +
        24*B^2*(Q:ℝ)^2/((F:ℝ)*X) := by
  have hα : 1/2≤1-H/X := by
    have hh : H/X≤1/2 := (div_le_iff₀ hX).mpr (by linarith)
    linarith
  have he (x : ℝ) : x-x*H/X=(1-H/X)*x := by ring
  simp_rw [actual_error_eq, he]
  exact difference_mean_square_bound Q a F hF B X (1-H/X) hX hα ha

run_cmd do
  for decl in [``term, ``aggregate, ``term_memLp, ``term_measurable,
      ``aggregate_measurable, ``aggregate_memLp, ``term_square_integrable,
      ``square_integrable, ``pointwise_le, ``integral_bound, ``actual_error_eq,
      ``scaled_square_integrable, ``norm_sub_square_le, ``difference_square_integrable,
      ``difference_mean_square_bound, ``moving_error_square_integrable, ``moving_error_bound] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "DIRECT MOVING ACTUAL AGGREGATE FOURIER TAIL BOUND PASSED"

end DirectMovingTailAggregate
