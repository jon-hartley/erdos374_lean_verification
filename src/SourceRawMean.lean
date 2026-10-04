import CancellationTransferResidual

/-! Literal source-cell regularity and conversion of a uniform raw second
mean to the exact sourceResidualAbs endpoint.
STATUS: NEW UNCOMPILED DRAFT, adapted from PositiveSharpCellMean.lean.
The analytic raw second-mean hypothesis remains explicit in this finite
adapter. Its proposed proof is in notes/SOURCE_RESIDUAL_ARGUMENT.md, not here.
No compiled full-source or unconditional Erdos theorem is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace SourceRawMean
open PositiveSharpCounts PositiveSharpResidual PositiveSharpMovingWindow
open PositiveSharpErrorMeasure PositiveInteriorModel PositiveInteriorCells
open CancellationTransferEndpoints CancellationTransferCenter CancellationTransferResidual

def rawDelta (X Y : ℝ) (j : ℕ × ℕ) (x : ℝ) : ℝ :=
  sourceCount X j x (x*Y/X)-(x*Y/X)*sourceMass j.1*sourceMass j.2

theorem sourceCount_eq_indicator_sum (X Y x : ℝ) (j : ℕ × ℕ) :
    sourceCount X j x (x*Y/X)=
      ∑ k ∈ sourceCoordinates X j, (movingSet X Y (tripleProduct k)).indicator
        (fun _ => tripleWeight k) x := by
  classical
  unfold sourceCount
  simp only [Finset.sum_filter, Set.indicator_apply]
  apply Finset.sum_congr rfl
  intro k _
  have he : x ∈ movingSet X Y (tripleProduct k) ↔ inWindow x (x*Y/X) k := Iff.rfl
  simp only [he]

theorem measurable_rawDelta (X Y : ℝ) (j : ℕ × ℕ) : Measurable (rawDelta X Y j) := by
  have hw : Measurable (fun x => sourceCount X j x (x*Y/X)) := by
    simp_rw [sourceCount_eq_indicator_sum]
    exact Finset.measurable_fun_sum _ (fun k _ =>
      measurable_const.indicator (movingSet_measurable X Y (tripleProduct k)))
  exact hw.sub (by fun_prop)

theorem sourceCount_nonneg (X x y : ℝ) (j : ℕ × ℕ) :
    0 ≤ sourceCount X j x y := by
  exact Finset.sum_nonneg (fun k _ => tripleWeight_nonneg k)

theorem sourceCount_le_full (X x y : ℝ) (j : ℕ × ℕ) :
    sourceCount X j x y≤∑ k∈sourceCoordinates X j, tripleWeight k := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro k _ _
  exact tripleWeight_nonneg k

theorem rawDelta_bound (X Y x : ℝ) (j : ℕ × ℕ) (hX : 0<X) (hY : 0<Y)
    (hx : x∈Icc X (2*X)) :
    |rawDelta X Y j x|≤(∑ k∈sourceCoordinates X j, tripleWeight k)+
      2*Y*|sourceMass j.1*sourceMass j.2| := by
  have hy := window_size_bounds X Y x hX hY.le hx
  unfold rawDelta
  calc
    _ ≤ |sourceCount X j x (x*Y/X)|+
        |(x*Y/X)*sourceMass j.1*sourceMass j.2| := abs_sub _ _
    _ ≤ _ := by
      rw [abs_of_nonneg (sourceCount_nonneg X x (x*Y/X) j),
        mul_assoc, abs_mul, abs_of_nonneg (hY.le.trans hy.1)]
      exact add_le_add (sourceCount_le_full X x (x*Y/X) j)
        (mul_le_mul_of_nonneg_right hy.2 (abs_nonneg _))

theorem rawDelta_integrable (X Y : ℝ) (j : ℕ × ℕ) (hX : 0<X) (hY : 0<Y) :
    IntegrableOn (rawDelta X Y j) (Icc X (2*X)) := by
  apply Measure.integrableOn_of_bounded isCompact_Icc.measure_lt_top.ne
    (measurable_rawDelta X Y j).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact rawDelta_bound X Y x j hX hY hx

theorem rawDelta_square_integrable (X Y : ℝ) (j : ℕ × ℕ) (hX : 0<X) (hY : 0<Y) :
    IntegrableOn (fun x => (rawDelta X Y j x)^2) (Icc X (2*X)) := by
  let B := (∑ k∈sourceCoordinates X j, tripleWeight k)+
    2*Y*|sourceMass j.1*sourceMass j.2|
  apply Measure.integrableOn_of_bounded isCompact_Icc.measure_lt_top.ne
    ((measurable_rawDelta X Y j).pow_const 2).aestronglyMeasurable (M := B^2)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
    (rawDelta_bound X Y x j hX hY hx) 2

theorem abs_integral_le_of_square (f : ℝ → ℝ) (X a : ℝ) (hX : 0<X) (ha : 0<a)
    (hf : IntegrableOn f (Icc X (2*X)))
    (hf2 : IntegrableOn (fun x => (f x)^2) (Icc X (2*X)))
    (hb : (∫ x in Icc X (2*X), (f x)^2)≤X*a^2) :
    (∫ x in Icc X (2*X), |f x|)≤X*a := by
  have hc : IntegrableOn (fun _ : ℝ => a^2) (Icc X (2*X)) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hm := setIntegral_mono_on (hf.abs.const_mul (2*a)) (hf2.add hc)
    measurableSet_Icc (fun x (_hx : x∈Icc X (2*X)) => by
      change 2*a*|f x|≤(f x)^2+a^2
      nlinarith [sq_nonneg (|f x|-a), sq_abs (f x)])
  change (∫ x in Icc X (2*X), 2*a*|f x|)≤
    (∫ x in Icc X (2*X), (f x)^2+a^2) at hm
  rw [integral_const_mul, integral_add hf2 hc, setIntegral_const,
    Real.volume_real_Icc_of_le (by linarith : X≤2*X), smul_eq_mul] at hm
  nlinarith

theorem raw_abs_integral_bound (X Y C : ℝ) (j : ℕ × ℕ)
    (hX : 1<X) (hY : 0<Y) (hC : 0<C)
    (hb : (∫ x in Icc X (2*X), (rawDelta X Y j x)^2)≤
      C^2*X*Y^2/(Real.log X)^2) :
    (∫ x in Icc X (2*X), |rawDelta X Y j x|)≤X*(C*Y/Real.log X) := by
  have hXp : 0<X := by linarith
  apply abs_integral_le_of_square _ X (C*Y/Real.log X) hXp
    (div_pos (mul_pos hC hY) (Real.log_pos hX))
    (rawDelta_integrable X Y j hXp hY) (rawDelta_square_integrable X Y j hXp hY)
  convert hb using 1; ring

theorem cell_abs_integral_bound (X Y C : ℝ) (j : ℕ × ℕ)
    (hX : 1<X) (hY : 0<Y) (hC : 0<C) (hj : j∈boxes (mesh X))
    (hb : (∫ x in Icc X (2*X), (rawDelta X Y j x)^2)≤
      C^2*X*Y^2/(Real.log X)^2) :
    (∫ x in Icc X (2*X), |sourceResidual X j x (x*Y/X)|)/X≤
      96*C/(Real.log X)^4 := by
  have hXp : 0<X := by linarith
  have hl : 0<Real.log X := Real.log_pos hX
  have hd := denominator_lower X hX j hj
  have hdp : 0<denominator X j := (by positivity : 0<(Real.log X)^3/96).trans_le hd
  have hm := setIntegral_mono_on
    (sourceResidual_integrable X Y hXp hY j).abs
    ((rawDelta_integrable X Y j hXp hY).abs.div_const (Y*denominator X j))
    measurableSet_Icc (fun x (hx : x∈Icc X (2*X)) => by
      have hy := (window_size_bounds X Y x hXp hY.le hx).1
      change |rawDelta X Y j x/((x*Y/X)*denominator X j)|≤_
      rw [abs_div, abs_of_pos (mul_pos (hY.trans_le hy) hdp)]
      exact div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hY hdp)
        (mul_le_mul_of_nonneg_right hy hdp.le))
  rw [integral_div] at hm
  have hab := raw_abs_integral_bound X Y C j hX hY hC hb
  have hf : (∫ x in Icc X (2*X), |sourceResidual X j x (x*Y/X)|)≤
      X*C/(Real.log X*denominator X j) := by
    apply hm.trans
    calc
      _ ≤ (X*(C*Y/Real.log X))/(Y*denominator X j) :=
        div_le_div_of_nonneg_right hab (mul_pos hY hdp).le
      _ = _ := by field_simp
  have hf' : (∫ x in Icc X (2*X), |sourceResidual X j x (x*Y/X)|)/X≤
      C/(Real.log X*denominator X j) := by
    have hh := div_le_div_of_nonneg_right hf hXp.le
    convert hh using 1; field_simp
  apply hf'.trans
  apply (div_le_div_iff₀ (mul_pos hl hdp) (pow_pos hl 4)).mpr
  have hh := mul_le_mul_of_nonneg_left hd
    (show 0≤96*C*Real.log X by positivity)
  nlinarith

theorem source_mean_of_cell_second_moments (X Y C : ℝ)
    (hX : 1<X) (hY : 0<Y) (hC : 0<C) (hm : mesh X≤1/1000000)
    (hb : ∀ j∈boxes (mesh X),
      (∫ x in Icc X (2*X), (rawDelta X Y j x)^2)≤C^2*X*Y^2/(Real.log X)^2) :
    (∫ x in Icc X (2*X), sourceResidualAbs X x (x*Y/X))/X≤
      (96/45)*C/(Real.log X)^2 := by
  have hXp : 0<X := by linarith
  have hl : 0<Real.log X := Real.log_pos hX
  unfold sourceResidualAbs
  rw [integral_finsetSum _ (fun j _ => (sourceResidual_integrable X Y hXp hY j).abs),
    Finset.sum_div]
  calc
    _ ≤ ∑ _j∈boxes (mesh X), 96*C/(Real.log X)^4 :=
      Finset.sum_le_sum (fun j hj => cell_abs_integral_bound X Y C j hX hY hC hj (hb j hj))
    _ = (((boxes (mesh X)).card:ℝ)/(Real.log X)^2)*(96*C/(Real.log X)^2) := by
      simp; ring
    _ ≤ (1/45)*(96*C/(Real.log X)^2) :=
      mul_le_mul_of_nonneg_right (cell_card_normalized_bound X hX hm) (by positivity)
    _ = _ := by ring

/-- Exact normalization of the power-30 raw bound proved in the paper-level
argument. This adapter does not construct its raw-mean hypothesis. -/
theorem source_mean_of_power_thirty (X Y : ℝ)
    (hX : 1 < X) (hY : 0 < Y) (hm : mesh X ≤ 1/1000000)
    (hb : ∀ j ∈ boxes (mesh X),
      (∫ x in Icc X (2*X), (rawDelta X Y j x)^2) ≤ X*Y^2/(Real.log X)^30) :
    (∫ x in Icc X (2*X), sourceResidualAbs X x (x*Y/X))/X ≤
      (96/45)/(Real.log X)^16 := by
  have hl : 0 < Real.log X := Real.log_pos hX
  have hh := source_mean_of_cell_second_moments X Y (1/(Real.log X)^14)
    hX hY (by positivity) hm (by
      intro j hj
      convert hb j hj using 1 <;> field_simp <;> ring)
  calc
    _ ≤ (96/45)*(1/(Real.log X)^14)/(Real.log X)^2 := hh
    _ = _ := by field_simp <;> ring

run_cmd do
  for decl in [``sourceCount_eq_indicator_sum, ``measurable_rawDelta,
      ``sourceCount_nonneg, ``sourceCount_le_full, ``rawDelta_bound, ``rawDelta_integrable,
      ``rawDelta_square_integrable, ``abs_integral_le_of_square,
      ``raw_abs_integral_bound, ``cell_abs_integral_bound,
      ``source_mean_of_cell_second_moments, ``source_mean_of_power_thirty] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "LITERAL SOURCE RAW MEAN ADAPTER; ANALYTIC SECOND MEAN REMAINS AN EXPLICIT PREMISE"
end SourceRawMean
end
