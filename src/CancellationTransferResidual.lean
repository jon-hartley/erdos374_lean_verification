import CancellationTransferCenter

/-! Unconditional source/actual residual transfer, including the exact
dyadic reciprocal-mass center. This does not estimate either residual itself. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators
namespace CancellationTransferResidual
open PositiveInteriorModel PositiveInteriorCells PositiveSharpResidual
open PositiveSharpMovingWindow PositiveSharpErrorMeasure
open CancellationTransferEndpoints CancellationTransferEndpointMean CancellationTransferCenter

def residualDiscrepancy (X x y : ℝ) : ℝ :=
  ∑ j∈boxes (mesh X),|cellResidual X j x y-sourceResidual X j x y|

theorem sourceResidual_integrable (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (j : ℕ×ℕ) :
    IntegrableOn (fun x => sourceResidual X j x (x*Y/X)) (Icc X (2*X)) := by
  have he : IntegrableOn (fun x => endpointCell X j x (x*Y/X)) (Icc X (2*X)) := by
    simp_rw [endpointCell_eq_kernels]
    exact (kernelSum_integrable _ X Y _ hX hY).sub (kernelSum_integrable _ X Y _ hX hY)
  have hc : IntegrableOn (fun _ : ℝ => centerCell X j) (Icc X (2*X)) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  apply (((cellResidual_integrable X Y hX hY j).add he).sub hc).congr_fun
  · intro x hx
    have hy : 0<x*Y/X := div_pos (mul_pos (hX.trans_le hx.1) hY) hX
    exact (sourceResidual_eq X x (x*Y/X) hy.ne' j).symm
  · exact measurableSet_Icc

theorem sourceResidualAbs_integrable (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    IntegrableOn (fun x => sourceResidualAbs X x (x*Y/X)) (Icc X (2*X)) :=
  integrable_finsetSum _ (fun j _ => (sourceResidual_integrable X Y hX hY j).abs)

theorem residualDiscrepancy_integrable (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    IntegrableOn (fun x => residualDiscrepancy X x (x*Y/X)) (Icc X (2*X)) :=
  integrable_finsetSum _ (fun j _ => ((cellResidual_integrable X Y hX hY j).sub
    (sourceResidual_integrable X Y hX hY j)).abs)

theorem discrepancy_le (X x y : ℝ) (hX : 1<X) (hm : mesh X≤1/8) (hy : y≠0) :
    residualDiscrepancy X x y≤endpointTotal X x y+centerTotal X := by
  unfold residualDiscrepancy endpointTotal centerTotal
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  rw [sourceResidual_eq X x y hy j,
    show cellResidual X j x y-(cellResidual X j x y+endpointCell X j x y-centerCell X j)=
      centerCell X j-endpointCell X j x y by ring]
  have hh := abs_sub (centerCell X j) (endpointCell X j x y)
  rw [abs_of_nonneg (centerCell_nonneg X hX hm j hj)] at hh
  linarith

theorem discrepancy_mean_le (X Y : ℝ) (hX : 1<X) (hm : mesh X≤1/8) (hY : 0<Y) :
    (∫x in Icc X (2*X),residualDiscrepancy X x (x*Y/X))/X≤
      (∫x in Icc X (2*X),endpointTotal X x (x*Y/X))/X+centerTotal X := by
  have hXp : 0<X := by linarith
  have he := endpointTotal_integrable X Y hXp hY
  have hc : IntegrableOn (fun _ : ℝ => centerTotal X) (Icc X (2*X)) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hh := setIntegral_mono_on (residualDiscrepancy_integrable X Y hXp hY)
    (he.add hc) measurableSet_Icc (fun x (hx : x∈Icc X (2*X)) =>
      discrepancy_le X x (x*Y/X) hX hm (div_pos (mul_pos (hXp.trans_le hx.1) hY) hXp).ne')
  simp only [Pi.add_apply] at hh
  rw [integral_add he hc,setIntegral_const,
    Real.volume_real_Icc_of_le (by linarith : X≤2*X),smul_eq_mul] at hh
  have hd := div_le_div_of_nonneg_right hh hXp.le
  have heq : ((∫x in Icc X (2*X),endpointTotal X x (x*Y/X))+
      (2*X-X)*centerTotal X)/X =
      (∫x in Icc X (2*X),endpointTotal X x (x*Y/X))/X+centerTotal X := by
    generalize (∫x in Icc X (2*X),endpointTotal X x (x*Y/X)) = I
    field_simp
    ring
  exact hd.trans_eq heq

theorem eventually_discrepancy_mean : ∀ᶠ X : ℝ in atTop, 1<X ∧ ∀ Y : ℝ, 0<Y →
    (∫x in Icc X (2*X),residualDiscrepancy X x (x*Y/X))/X≤4101/X^((1:ℝ)/12) := by
  obtain ⟨X0,hX0,hb⟩ := actual_endpoint_mean_bound
  filter_upwards [eventually_ge_atTop X0,
    eventually_ge_atTop (Real.exp (1000000*Real.log 2)),
    PolynomialLogEnvelope.eventually_bound 1 1 (1/12) (by norm_num) (by norm_num)]
      with X hXX hXe he
  have hX : 1<X := by linarith
  have hXp : 0<X := by linarith
  have hell : 0<Real.log X := Real.log_pos hX
  have hlog : 1000000*Real.log 2≤Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hXe
  have hm : mesh X≤1/1000000 := by
    unfold mesh
    apply (div_le_iff₀ hell).mpr
    linarith
  have hsmall : Real.log X≤X^((1:ℝ)/12) := by simpa using (le_trans (by simp) he.2)
  have hp : 0<X^((1:ℝ)/12) := Real.rpow_pos_of_pos hXp _
  have heq : X^((1:ℝ)/6)=X^((1:ℝ)/12)*X^((1:ℝ)/12) := by
    rw [←Real.rpow_add hXp]
    norm_num
  have hc : centerTotal X≤5/X^((1:ℝ)/12) := by
    apply (centerTotal_le X hX hm).trans
    rw [heq]
    calc
      _ ≤ 5*X^((1:ℝ)/12)/(X^((1:ℝ)/12)*X^((1:ℝ)/12)) := by gcongr
      _ = _ := by field_simp
  refine ⟨hX,?_⟩
  intro Y hY
  have ht := (discrepancy_mean_le X Y hX (by linarith) hY).trans
    (add_le_add (hb X hXX Y hY) hc)
  convert ht using 1
  ring

theorem residualAbs_difference_le (X x y : ℝ) :
    |residualAbs X x y-sourceResidualAbs X x y|≤residualDiscrepancy X x y := by
  unfold residualAbs sourceResidualAbs residualDiscrepancy
  rw [←Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ =>
    abs_abs_sub_abs_le_abs_sub _ _))

theorem residual_means_difference_le (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    |(∫x in Icc X (2*X),residualAbs X x (x*Y/X))/X-
      (∫x in Icc X (2*X),sourceResidualAbs X x (x*Y/X))/X|≤
        (∫x in Icc X (2*X),residualDiscrepancy X x (x*Y/X))/X := by
  have ha := residualAbs_integrable X Y hX hY
  have hb := sourceResidualAbs_integrable X Y hX hY
  rw [←sub_div,←integral_sub ha hb,abs_div,abs_of_pos hX]
  apply div_le_div_of_nonneg_right _ hX.le
  exact (abs_integral_le_integral_abs).trans
    (setIntegral_mono_on (ha.sub hb).abs (residualDiscrepancy_integrable X Y hX hY)
      measurableSet_Icc (fun x _ => residualAbs_difference_le X x (x*Y/X)))

theorem eventually_residual_transfer_log (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ ∀ Y : ℝ, 0<Y →
      |(∫x in Icc X (2*X),residualAbs X x (x*Y/X))/X-
        (∫x in Icc X (2*X),sourceResidualAbs X x (x*Y/X))/X|≤1/(Real.log X)^A := by
  filter_upwards [eventually_discrepancy_mean,
    PolynomialLogEnvelope.eventually_bound 4101 A (1/12) (by norm_num) (by norm_num)]
      with X hb he
  have hX : 0<X := by linarith [hb.1]
  have hl : 0<Real.log X := Real.log_pos hb.1
  have hp : 0<X^((1:ℝ)/12) := Real.rpow_pos_of_pos hX _
  have hlog : 4101*(Real.log X)^A≤X^((1:ℝ)/12) := by
    apply le_trans _ he.2
    gcongr
    linarith
  refine ⟨hb.1,?_⟩
  intro Y hY
  exact ((residual_means_difference_le X Y hX hY).trans (hb.2 Y hY)).trans
    ((div_le_div_iff₀ hp (pow_pos hl A)).mpr (by simpa using hlog))

run_cmd do
  for decl in [``sourceResidual_integrable,``sourceResidualAbs_integrable,
      ``residualDiscrepancy_integrable,``discrepancy_le,``discrepancy_mean_le,
      ``eventually_discrepancy_mean,``residualAbs_difference_le,
      ``residual_means_difference_le,``eventually_residual_transfer_log] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL/SOURCE SHARP RESIDUAL L1 TRANSFER: ALL LOG POWERS; ANALYTIC SAVING STILL OPEN"
end CancellationTransferResidual
end
