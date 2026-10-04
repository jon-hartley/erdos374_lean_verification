import Item1NormalizedPhysical
import SourceRawMean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! UNCOMPILED, 2026-10-02. Square-root-free aggregation and the LITERAL
sourceResidualAbs interface. The final theorem retains TWO quantitative budgets:
the constructed selected spectrum's total energy and the constructed physical
bad-tuple first mean. They are not proved small by this module. The preceding
source proofs construct the physical second mean instead of assuming it.
-/
set_option autoImplicit false
set_option maxHeartbeats 26000000
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
namespace Item1QuadraticAssembly
open Item1SelectedWindow Item1SelectedFourier Item1NormalizedPhysical
open PositiveSharpCounts PositiveInteriorModel PositiveInteriorCells
open PositiveSharpMovingWindow
open CancellationTransferEndpoints CancellationTransferCenter CancellationTransferResidual

/-- This elementary inequality avoids square roots in the endpoint adapter. -/
theorem young_fixed (ell z : ℝ) (hl : 0<ell) :
    |z| ≤ ell*z^2+1/(4*ell) := by
  have hs := sq_nonneg (2*ell*|z|-1)
  have hs' : 4*ell*|z| ≤ 4*ell^2*z^2+1 := by
    nlinarith [sq_abs z]
  have hh := div_le_div_of_nonneg_right hs' (show 0≤4*ell by positivity)
  convert hh using 1 <;> field_simp <;> ring

theorem denominator_young (ell d z : ℝ) (hl : 0<ell) (hd : ell^3/96≤d) :
    |z|/d ≤ (96/ell^2)*z^2+24/ell^4 := by
  have hbase : 0<ell^3/96 := by positivity
  have hstep := div_le_div_of_nonneg_left (abs_nonneg z) hbase hd
  have hy := div_le_div_of_nonneg_right (young_fixed ell z hl) hbase.le
  apply hstep.trans (hy.trans_eq _)
  field_simp <;> ring

theorem cell_mean_young (r : ℝ→ℝ) (X ell d : ℝ) (hX : 0<X) (hl : 0<ell)
    (hd : ell^3/96≤d) (hr : IntegrableOn r (Icc X (2*X)))
    (hr2 : IntegrableOn (fun x => (r x)^2) (Icc X (2*X))) :
    (∫ x in Icc X (2*X), |r x|/d)/X ≤
      (96/ell^2)*((∫ x in Icc X (2*X), (r x)^2)/X)+24/ell^4 := by
  have hc : IntegrableOn (fun _ : ℝ => 24/ell^4) (Icc X (2*X)) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hm := setIntegral_mono_on (hr.abs.div_const d)
    ((hr2.const_mul (96/ell^2)).add hc) measurableSet_Icc
    (fun x _ => denominator_young ell d (r x) hl hd)
  simp only [Pi.add_apply] at hm
  rw [integral_add (hr2.const_mul (96/ell^2)) hc,integral_const_mul,setIntegral_const,
    Real.volume_real_Icc_of_le (by linarith : X≤2*X),smul_eq_mul] at hm
  have hh := div_le_div_of_nonneg_right hm hX.le
  convert hh using 1 <;> field_simp <;> ring

def primeCell (X Y : ℝ) (j : ℕ×ℕ) (x : ℝ) : ℝ :=
  selectedResidual X Y j (primeTuples X j) x/denominator X j

def badCell (X Y : ℝ) (j : ℕ×ℕ) (x : ℝ) : ℝ :=
  selectedCount (badTuples X j) x (x*Y/X)/((x*Y/X)*denominator X j)

def primeMean (X Y : ℝ) : ℝ :=
  (∫ x in Icc X (2*X), ∑ j ∈ boxes (mesh X), |primeCell X Y j x|)/X

def badMean (X Y : ℝ) : ℝ :=
  (∫ x in Icc X (2*X), ∑ j ∈ boxes (mesh X), badCell X Y j x)/X

def totalEnergy (X Y : ℝ) : ℝ :=
  ∑ j ∈ boxes (mesh X), energy X Y j (primeTuples X j)

theorem totalEnergy_nonneg (X Y : ℝ) : 0≤totalEnergy X Y := by
  apply Finset.sum_nonneg
  intro j _
  exact integral_nonneg (fun _ => sq_nonneg _)

theorem cell_denominator_pos (X : ℝ) (j : ℕ×ℕ) (hX : 1<X)
    (hj : j∈boxes (mesh X)) : 0<denominator X j := by
  have hl : 0<Real.log X := Real.log_pos hX
  exact (by positivity : 0<(Real.log X)^3/96).trans_le (denominator_lower X hX j hj)

theorem primeCell_integrable (X Y : ℝ) (j : ℕ×ℕ)
    (hX : 0<X) (hY : 0<Y) (hYX : Y≤X/2) :
    IntegrableOn (primeCell X Y j) (Icc X (2*X)) :=
  (selectedResidual_integrable X Y j (primeTuples X j) (primeTuples_subset X j)
    hX hY hYX).div_const _

theorem source_cell_partition (X Y x : ℝ) (j : ℕ×ℕ) (hX : 1<X)
    (hj : j∈boxes (mesh X)) (hx : x∈Icc X (2*X)) (hY : 0<Y) :
    sourceResidual X j x (x*Y/X)=primeCell X Y j x+badCell X Y j x := by
  have hXp : 0<X := by linarith
  have hxp : 0<x := hXp.trans_le hx.1
  have hy : 0<x*Y/X := by positivity
  have hd := cell_denominator_pos X j hX hj
  change (sourceCount X j x (x*Y/X)-(x*Y/X)*sourceMass j.1*sourceMass j.2)/
    ((x*Y/X)*denominator X j) = _
  rw [←count_partition X x (x*Y/X) j]
  unfold primeCell badCell selectedResidual
  field_simp [hy.ne',hd.ne'] <;> ring

theorem badCell_nonneg (X Y x : ℝ) (j : ℕ×ℕ) (hX : 1<X)
    (hj : j∈boxes (mesh X)) (hx : x∈Icc X (2*X)) (hY : 0<Y) :
    0≤badCell X Y j x := by
  have hXp : 0<X := by linarith
  have hxp : 0<x := hXp.trans_le hx.1
  exact div_nonneg (selectedCount_nonneg _ _ _)
    (mul_nonneg (by positivity) (cell_denominator_pos X j hX hj).le)

theorem badCell_integrable (X Y : ℝ) (j : ℕ×ℕ) (hX : 1<X)
    (hj : j∈boxes (mesh X)) (hY : 0<Y) (hYX : Y≤X/2) :
    IntegrableOn (badCell X Y j) (Icc X (2*X)) := by
  have hp := primeCell_integrable X Y j (by linarith) hY hYX
  have hs := sourceResidual_integrable X Y (by linarith : 0<X) hY j
  apply (hs.sub hp).congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  simp only [Pi.sub_apply]
  rw [source_cell_partition X Y x j hX hj hx hY]
  ring

/-- Actual-cell aggregation: ell^{-2}, not ell^{+2}, outside the spectral budget. -/
theorem primeMean_le_quadratic (X Y : ℝ) (hX : 2≤X)
    (hlog : 1000000≤Real.log X) (hm : mesh X≤1/1000000)
    (hY : 0<Y) (hYX : Y≤X/2) :
    primeMean X Y ≤ (96*totalEnergy X Y/Real.pi+8/15)/(Real.log X)^2 := by
  have hX1 : 1<X := by linarith
  have hXp : 0<X := by linarith
  have hl : 0<Real.log X := Real.log_pos hX1
  have hcell (j : ℕ×ℕ) (hj : j∈boxes (mesh X)) :
      (∫ x in Icc X (2*X), |primeCell X Y j x|)/X ≤
        (96/(Real.log X)^2)*(energy X Y j (primeTuples X j)/Real.pi)+
          24/(Real.log X)^4 := by
    have hd := cell_denominator_pos X j hX1 hj
    have hy := cell_mean_young (selectedResidual X Y j (primeTuples X j)) X
      (Real.log X) (denominator X j) hXp hl (denominator_lower X hX1 j hj)
      (selectedResidual_integrable X Y j _ (primeTuples_subset X j) hXp hY hYX)
      (selectedResidual_square_integrable X Y j _ (primeTuples_subset X j) hXp hY hYX)
    have hs := selected_second_mean X Y j (primeTuples X j) (primeTuples_subset X j)
      hX hlog hj hY hYX
    have he (x : ℝ) : |primeCell X Y j x|=
        |selectedResidual X Y j (primeTuples X j) x|/denominator X j := by
      rw [primeCell,abs_div,abs_of_pos hd]
    simp_rw [←he] at hy
    exact hy.trans (add_le_add (mul_le_mul_of_nonneg_left hs
      (show 0 ≤ 96/(Real.log X)^2 by positivity)) le_rfl)
  unfold primeMean
  rw [integral_finsetSum _ (fun j _ => (primeCell_integrable X Y j hXp hY hYX).abs),
    Finset.sum_div]
  have hh := Finset.sum_le_sum hcell
  have hc := mul_le_mul_of_nonneg_right (cell_card_normalized_bound X hX1 hm)
    (show 0≤24/(Real.log X)^2 by positivity)
  have hsums : (∑ j ∈ boxes (mesh X),
      ((96/(Real.log X)^2)*(energy X Y j (primeTuples X j)/Real.pi)+24/(Real.log X)^4)) =
      (96/(Real.log X)^2)*(totalEnergy X Y/Real.pi)+
        (((boxes (mesh X)).card:ℝ)/(Real.log X)^2)*(24/(Real.log X)^2) := by
    simp only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_div,totalEnergy,
      Finset.sum_const,nsmul_eq_mul]
    ring
  rw [hsums] at hh
  apply hh.trans
  calc
    _ ≤ (96/(Real.log X)^2)*(totalEnergy X Y/Real.pi)+(1/45)*(24/(Real.log X)^2) :=
      add_le_add le_rfl hc
    _ = _ := by ring

/-- The original residual, not a replacement definition, is bounded here. -/
theorem literal_mean_le_prime_add_bad (X Y : ℝ) (hX : 1<X)
    (hY : 0<Y) (hYX : Y≤X/2) :
    (∫ x in Icc X (2*X), sourceResidualAbs X x (x*Y/X))/X ≤
      primeMean X Y+badMean X Y := by
  have hXp : 0<X := by linarith
  have hi0 := integrable_finsetSum (boxes (mesh X))
    (fun j _ => (sourceResidual_integrable X Y hXp hY j).abs)
  have hi1 := integrable_finsetSum (boxes (mesh X))
    (fun j _ => (primeCell_integrable X Y j hXp hY hYX).abs)
  have hi2 := integrable_finsetSum (boxes (mesh X))
    (fun j hj => badCell_integrable X Y j hX hj hY hYX)
  have hp (x : ℝ) (hx : x∈Icc X (2*X)) :
      sourceResidualAbs X x (x*Y/X) ≤
        (∑ j ∈ boxes (mesh X), |primeCell X Y j x|)+
          ∑ j ∈ boxes (mesh X), badCell X Y j x := by
    unfold sourceResidualAbs
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j hj
    rw [source_cell_partition X Y x j hX hj hx hY]
    simpa only [Real.norm_eq_abs, abs_of_nonneg (badCell_nonneg X Y x j hX hj hx hY)] using
      norm_add_le (primeCell X Y j x) (badCell X Y j x)
  have hh := setIntegral_mono_on hi0 (hi1.add hi2) measurableSet_Icc hp
  simp only [Pi.add_apply] at hh
  rw [integral_add hi1 hi2] at hh
  have hd := div_le_div_of_nonneg_right hh hXp.le
  simpa only [primeMean,badMean,sourceResidualAbs,add_div] using hd

/-- Fixed-budget target for the maintained Item 1 interface.
This is CONDITIONAL on the TWO displayed small-budget hypotheses.
It does not prove the prime cap, the moment certificate, or the deletion bound. -/
theorem literal_item1_of_two_budgets (X Y : ℝ) (hX : 2≤X)
    (hlog : 1000000≤Real.log X) (hm : mesh X≤1/1000000)
    (hY : 0<Y) (hYX : Y≤X/2)
    (hE : totalEnergy X Y≤1/1024)
    (hB : badMean X Y≤1/(4*(Real.log X)^2)) :
    (∫ x in Icc X (2*X), sourceResidualAbs X x (x*Y/X))/X ≤ 1/(Real.log X)^2 := by
  have hl : 0<Real.log X := by linarith
  have hpi : 1≤Real.pi := by linarith [Real.pi_gt_three]
  have he : totalEnergy X Y/Real.pi≤1/1024 := by
    have hh := div_le_div_of_nonneg_left (totalEnergy_nonneg X Y) (by norm_num : (0:ℝ)<1) hpi
    have hh' : totalEnergy X Y/Real.pi≤totalEnergy X Y := by simpa only [div_one] using hh
    exact hh'.trans hE
  have hc : 96*totalEnergy X Y/Real.pi+8/15+1/4≤421/480 := by
    have hh := mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ) ≤ 96)
    rw [←mul_div_assoc] at hh
    linarith only [hh]
  calc
    _ ≤ primeMean X Y+badMean X Y :=
      literal_mean_le_prime_add_bad X Y (by linarith) hY hYX
    _ ≤ (96*totalEnergy X Y/Real.pi+8/15)/(Real.log X)^2+
        1/(4*(Real.log X)^2) :=
      add_le_add (primeMean_le_quadratic X Y hX hlog hm hY hYX) hB
    _ = (96*totalEnergy X Y/Real.pi+8/15+1/4)/(Real.log X)^2 := by ring
    _ ≤ (421/480)/(Real.log X)^2 := div_le_div_of_nonneg_right hc (sq_nonneg _)
    _ ≤ 1/(Real.log X)^2 := div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _)

end Item1QuadraticAssembly


run_cmd do
  for target in [``Item1QuadraticAssembly.young_fixed,
    ``Item1QuadraticAssembly.denominator_young,
    ``Item1QuadraticAssembly.cell_mean_young,
    ``Item1QuadraticAssembly.totalEnergy_nonneg,
    ``Item1QuadraticAssembly.cell_denominator_pos,
    ``Item1QuadraticAssembly.primeCell_integrable,
    ``Item1QuadraticAssembly.source_cell_partition,
    ``Item1QuadraticAssembly.badCell_nonneg,
    ``Item1QuadraticAssembly.badCell_integrable,
    ``Item1QuadraticAssembly.primeMean_le_quadratic,
    ``Item1QuadraticAssembly.literal_mean_le_prime_add_bad,
    ``Item1QuadraticAssembly.literal_item1_of_two_budgets] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
