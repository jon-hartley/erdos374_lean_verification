import PositiveSharpMovingWindow

/-! Integrability and Markov control of the literal sharp-window error.
The residual mean remains an explicit premise. The prime-power deletion
mean is supplied by the proved moving-window theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace PositiveSharpErrorMeasure
open PositiveInteriorModel PositiveInteriorCells
open PositiveSharpCounts PositiveSharpResidual PositiveSharpMovingWindow

def error (X Y x : ℝ) : ℝ :=
  residualAbs X x (x*Y/X)+deletionTotal X x (x*Y/X)

def badSet (X Y ε : ℝ) : Set ℝ :=
  {x | ε/Real.log X < error X Y x} ∩ Icc X (2*X)

theorem weightedCount_eq_kernel_sum (X Y x : ℝ) (j : ℕ × ℕ) :
    weightedCount X j x (x*Y/X)/((x*Y/X)*denominator X j)=
      ∑ k ∈ coordinates X j,
        (tripleWeight k/denominator X j)*movingKernel X Y (tripleProduct k) x := by
  classical
  unfold weightedCount windowTuples
  simp only [Finset.sum_filter, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  have he : x ∈ movingSet X Y (tripleProduct k) ↔ inWindow x (x*Y/X) k := Iff.rfl
  simp only [movingKernel, Set.indicator_apply, he]
  by_cases hw : inWindow x (x*Y/X) k
  · simp [hw]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  · simp [hw]

theorem normalized_weightedCount_integrable (X Y : ℝ) (hX : 0<X) (hY : 0<Y)
    (j : ℕ × ℕ) :
    IntegrableOn (fun x => weightedCount X j x (x*Y/X)/((x*Y/X)*denominator X j))
      (Icc X (2*X)) := by
  simp_rw [weightedCount_eq_kernel_sum]
  exact integrable_finsetSum _ (fun k _ =>
    (movingKernel_integrable X Y (tripleProduct k) hX hY).const_mul _)

theorem cellResidual_eq_normalized (X x y : ℝ) (hy : y≠0) (j : ℕ × ℕ) :
    cellResidual X j x y=
      weightedCount X j x y/(y*denominator X j)-cellModel X j := by
  unfold cellResidual cellModel
  rw [sub_div, mul_assoc, mul_div_mul_left _ _ hy]

theorem cellResidual_integrable (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (j : ℕ × ℕ) :
    IntegrableOn (fun x => cellResidual X j x (x*Y/X)) (Icc X (2*X)) := by
  have hc : IntegrableOn (fun _ : ℝ => cellModel X j) (Icc X (2*X)) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  apply ((normalized_weightedCount_integrable X Y hX hY j).sub hc).congr_fun
    (hs := measurableSet_Icc)
  intro x hx
  exact (cellResidual_eq_normalized X x (x*Y/X)
    (div_pos (mul_pos (hX.trans_le hx.1) hY) hX).ne' j).symm

theorem residualAbs_integrable (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    IntegrableOn (fun x => residualAbs X x (x*Y/X)) (Icc X (2*X)) := by
  unfold residualAbs
  exact integrable_finsetSum _ (fun j _ => (cellResidual_integrable X Y hX hY j).abs)

theorem totalResidual_integrable (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    IntegrableOn (fun x => totalResidual X x (x*Y/X)) (Icc X (2*X)) := by
  unfold totalResidual
  exact integrable_finsetSum _ (fun j _ => cellResidual_integrable X Y hX hY j)

theorem error_integrable (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    IntegrableOn (error X Y) (Icc X (2*X)) :=
  (residualAbs_integrable X Y hX hY).add (deletionTotal_integrable X Y hX hY)

theorem error_nonneg (X Y x : ℝ) (hX : 1<X) (hY : 0<Y)
    (hx : x ∈ Icc X (2*X)) : 0≤error X Y x := by
  have hXp : 0<X := by linarith
  have hlog : 0<Real.log X := Real.log_pos hX
  have hy : 0<x*Y/X := div_pos (mul_pos (hXp.trans_le hx.1) hY) hXp
  have hd : 0≤deletionTotal X x (x*Y/X) := by
    apply Finset.sum_nonneg
    intro j hj
    have hp : 0<denominator X j :=
      (by positivity : 0<(Real.log X)^3/96).trans_le (denominator_lower X hX j hj)
    exact div_nonneg (deletionCount_nonneg X x (x*Y/X) j) (mul_pos hy hp).le
  exact add_nonneg (residualAbs_nonneg X x (x*Y/X)) hd

theorem error_integral_eq (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    (∫ x in Icc X (2*X), error X Y x)=
      (∫ x in Icc X (2*X), residualAbs X x (x*Y/X))+
      (∫ x in Icc X (2*X), deletionTotal X x (x*Y/X)) :=
  integral_add (residualAbs_integrable X Y hX hY) (deletionTotal_integrable X Y hX hY)

private theorem markov_on (f : ℝ → ℝ) (I : Set ℝ) (hI : MeasurableSet I)
    (hf : IntegrableOn f I) (hn : ∀ x ∈ I, 0≤f x) (g : ℝ) (hg : 0<g) :
    volume.real ({x | g<f x} ∩ I) ≤ (∫ x in I, f x)/g := by
  let normalized := fun x => f x/g
  have hi : Integrable normalized (volume.restrict I) := hf.div_const g
  have hp : 0≤ᵐ[volume.restrict I] normalized :=
    (ae_restrict_mem hI).mono (fun x hx => div_nonneg (hn x hx) hg.le)
  have hm := hi.measure_le_integral hp (s := {x | g<f x} ∩ I) (by
    intro x hx
    exact (le_div_iff₀ hg).mpr (by simpa using hx.1.le))
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
  rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hp)] at hr
  simpa [Measure.real, Measure.restrict_apply' hI, inter_assoc, normalized, integral_div] using hr

theorem badSet_measure_le (X Y ε : ℝ) (hX : 1<X) (hY : 0<Y) (hε : 0<ε) :
    volume.real (badSet X Y ε) ≤ (Real.log X/ε)*
      ((∫ x in Icc X (2*X), residualAbs X x (x*Y/X))+
       (∫ x in Icc X (2*X), deletionTotal X x (x*Y/X))) := by
  have hXp : 0<X := by linarith
  have hh := markov_on (error X Y) (Icc X (2*X)) measurableSet_Icc
    (error_integrable X Y hXp hY) (fun x hx => error_nonneg X Y x hX hY hx)
    (ε/Real.log X) (div_pos hε (Real.log_pos hX))
  rw [error_integral_eq X Y hXp hY] at hh
  simpa only [badSet, div_div_eq_mul_div, div_eq_mul_inv, mul_inv_rev, inv_inv,
    mul_comm, mul_left_comm, mul_assoc] using hh

theorem outside_badSet (X Y ε x : ℝ) (hx : x ∈ Icc X (2*X))
    (hgood : x ∉ badSet X Y ε) :
    residualAbs X x (x*Y/X)+deletionTotal X x (x*Y/X)≤ε/Real.log X := by
  by_contra hh
  exact hgood ⟨lt_of_not_ge hh, hx⟩

/-- A bound on the actual residual mean is an explicit premise. The deletion
mean is unconditional and comes from the literal finite prime-power deletion. -/
theorem actual_error_measure_bound :
    ∃ X0 : ℝ, 2≤X0 ∧ ∀ X : ℝ, X0≤X → ∀ Y ε B : ℝ, 0<Y → 0<ε →
      (∫ x in Icc X (2*X), residualAbs X x (x*Y/X))/X≤B →
      volume.real (badSet X Y ε)≤
        X*(Real.log X/ε)*(B+4096/X^((1:ℝ)/12)) := by
  obtain ⟨X0,hX0,hd⟩ := actual_total_deletion_mean_bound
  refine ⟨X0,hX0,?_⟩
  intro X hXX Y ε B hY hε hmean
  have hX : 1<X := by linarith [hX0.trans hXX]
  have hXp : 0<X := by linarith
  have hs := add_le_add hmean (hd X hXX Y hY)
  rw [← add_div] at hs
  have hs' := (div_le_iff₀ hXp).mp hs
  calc
    _ ≤ (Real.log X/ε)*
        ((∫ x in Icc X (2*X), residualAbs X x (x*Y/X))+
         (∫ x in Icc X (2*X), deletionTotal X x (x*Y/X))) :=
      badSet_measure_le X Y ε hX hY hε
    _ ≤ (Real.log X/ε)*((B+4096/X^((1:ℝ)/12))*X) :=
      mul_le_mul_of_nonneg_left hs' (div_nonneg (Real.log_pos hX).le hε.le)
    _ = _ := by ring

run_cmd do
  for decl in [``weightedCount_eq_kernel_sum, ``normalized_weightedCount_integrable,
      ``cellResidual_eq_normalized, ``cellResidual_integrable, ``residualAbs_integrable,
      ``totalResidual_integrable, ``error_integrable, ``error_nonneg, ``error_integral_eq,
      ``badSet_measure_le, ``outside_badSet, ``actual_error_measure_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL ERROR INTEGRABLE AND MARKOV BOUND; RESIDUAL MEAN SAVING REMAINS EXPLICIT"
end PositiveSharpErrorMeasure
end
