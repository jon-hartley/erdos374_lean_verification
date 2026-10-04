import PositiveSharpDeletionMass
import PositiveSharpResidual
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Moving sharp windows, with y=x*Y/X. All integrals below concern the
literal new-cell prime-power deletion. No tent-window estimate is imported
and no bound on the prime-inclusive count-minus-model residual is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace PositiveSharpMovingWindow
open PositiveInteriorModel PositiveInteriorCells PositiveInteriorRectangles
open PositiveSharpCounts PositiveSharpResidual

def movingSet (X Y n : ℝ) : Set ℝ := {x | x-x*Y/X<n ∧ n≤x}
def movingKernel (X Y n : ℝ) : ℝ → ℝ :=
  (movingSet X Y n).indicator (fun x => 1/(x*Y/X))

theorem movingSet_measurable (X Y n : ℝ) : MeasurableSet (movingSet X Y n) := by
  exact (isOpen_lt (continuous_id.sub ((continuous_id.mul_const Y).div_const X))
    continuous_const).measurableSet.inter measurableSet_Ici

theorem window_size_bounds (X Y x : ℝ) (hX : 0 < X) (hY : 0 ≤ Y)
    (hx : x ∈ Icc X (2*X)) : Y ≤ x*Y/X ∧ x*Y/X ≤ 2*Y := by
  constructor
  · apply (le_div_iff₀ hX).mpr
    nlinarith [mul_le_mul_of_nonneg_right hx.1 hY]
  · apply (div_le_iff₀ hX).mpr
    nlinarith [mul_le_mul_of_nonneg_right hx.2 hY]

theorem moving_support_subset (X Y n : ℝ) (hX : 0 < X) (hY : 0 < Y) :
    Icc X (2*X) ∩ movingSet X Y n ⊆ Icc n (n+4*Y) := by
  intro x hx
  have hb := window_size_bounds X Y x hX hY.le hx.1
  exact ⟨hx.2.2, by have hh := hx.2.1; linarith⟩

theorem movingKernel_integrable (X Y n : ℝ) (hX : 0 < X) (hY : 0 < Y) :
    IntegrableOn (movingKernel X Y n) (Icc X (2*X)) := by
  have hc : ContinuousOn (fun x : ℝ => 1/(x*Y/X)) (Icc X (2*X)) := by
    apply continuousOn_const.div ((continuousOn_id.mul_const Y).div_const X)
    intro x hx
    exact (div_pos (mul_pos (hX.trans_le hx.1) hY) hX).ne'
  exact (hc.integrableOn_compact isCompact_Icc).indicator (movingSet_measurable X Y n)

theorem movingKernel_integral_le (X Y n : ℝ) (hX : 0 < X) (hY : 0 < Y) :
    (∫ x in Icc X (2*X), movingKernel X Y n x) ≤ 4 := by
  classical
  let g : ℝ → ℝ := (Icc n (n+4*Y)).indicator (fun _ => 1/Y)
  have hg : Integrable g :=
    (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) :
      IntegrableOn (fun _ : ℝ => 1/Y) (Icc n (n+4*Y))).integrable_indicator
      measurableSet_Icc
  have hgn : ∀ x, 0 ≤ g x := by
    intro x
    exact Set.indicator_nonneg (fun _ _ => by positivity) x
  calc
    _ ≤ ∫ x in Icc X (2*X), g x := by
      apply setIntegral_mono_on (movingKernel_integrable X Y n hX hY) hg.integrableOn
        measurableSet_Icc
      intro x hx
      by_cases hn : x ∈ movingSet X Y n
      · have hm := moving_support_subset X Y n hX hY ⟨hx,hn⟩
        rw [movingKernel, Set.indicator_of_mem hn]
        change 1/(x*Y/X) ≤ (Icc n (n+4*Y)).indicator (fun _ => 1/Y) x
        rw [Set.indicator_of_mem hm]
        exact one_div_le_one_div_of_le hY (window_size_bounds X Y x hX hY.le hx).1
      · rw [movingKernel, Set.indicator_of_notMem hn]
        exact hgn x
    _ ≤ ∫ x, g x := setIntegral_le_integral hg (Filter.Eventually.of_forall hgn)
    _ = 4 := by
      dsimp only [g]
      rw [integral_indicator_const _ measurableSet_Icc,
        Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
      field_simp
      ring

theorem denominator_lower (X : ℝ) (hX : 1 < X) (j : ℕ × ℕ)
    (hj : j ∈ boxes (mesh X)) : (Real.log X)^3/96 ≤ denominator X j := by
  have hm := (mesh_pos X hX).le
  have hc := component_bounds _ _ (box_interior (mesh X) (mesh_pos X hX) j hj)
  have h₁ : (1/4:ℝ) ≤ (j.1:ℝ)*mesh X+mesh X := by linarith [hc.1]
  have h₂ : (1/4:ℝ) ≤ (j.2:ℝ)*mesh X+mesh X := by linarith [hc.2.1]
  have h₃ : (1/6:ℝ) ≤ 1-(j.1:ℝ)*mesh X-(j.2:ℝ)*mesh X+3*mesh X := by
    linarith [hc.2.2]
  have hprod : (1/96:ℝ) ≤
      ((j.1:ℝ)*mesh X+mesh X)*((j.2:ℝ)*mesh X+mesh X)*
        (1-(j.1:ℝ)*mesh X-(j.2:ℝ)*mesh X+3*mesh X) := by
    calc
      _ = (1/4:ℝ)*(1/4)*(1/6) := by norm_num
      _ ≤ _ := by gcongr
  rw [denominator_identity X hX j]
  have hh := mul_le_mul_of_nonneg_left hprod (pow_nonneg (Real.log_pos hX).le 3)
  simpa only [mul_one_div] using hh

theorem deletionCell_eq_kernel_sum (X Y x : ℝ) (j : ℕ × ℕ) :
    deletionCell X j x (x*Y/X)=
      ∑ k ∈ (coordinates X j).filter (fun k => ¬PositiveSharpCounts.allPrime k),
        (tripleWeight k/denominator X j)*movingKernel X Y (tripleProduct k) x := by
  classical
  unfold deletionCell deletionCount windowTuples
  simp only [Finset.sum_filter, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  have he : x ∈ movingSet X Y (tripleProduct k) ↔ inWindow x (x*Y/X) k := Iff.rfl
  simp only [movingKernel, Set.indicator_apply, he]
  by_cases hw : inWindow x (x*Y/X) k <;> by_cases hp : PositiveSharpCounts.allPrime k <;>
    simp [hw, hp]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem deletionCell_integrable (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y) (j : ℕ × ℕ) :
    IntegrableOn (fun x => deletionCell X j x (x*Y/X)) (Icc X (2*X)) := by
  simp_rw [deletionCell_eq_kernel_sum]
  exact integrable_finsetSum _ (fun k _ =>
    (movingKernel_integrable X Y (tripleProduct k) hX hY).const_mul _)

theorem deletionTotal_integrable (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y) :
    IntegrableOn (fun x => deletionTotal X x (x*Y/X)) (Icc X (2*X)) := by
  unfold deletionTotal
  exact integrable_finsetSum _ (fun j _ => deletionCell_integrable X Y hX hY j)

theorem deletion_integral_le_mass (X Y : ℝ) (hX : 1 < X) (hY : 0 < Y)
    (j : ℕ × ℕ) (hj : j ∈ boxes (mesh X)) :
    (∫ x in Icc X (2*X), deletionCell X j x (x*Y/X)) ≤
      4/denominator X j*PositiveSharpDeletionMass.cellBadMass X j := by
  have hXp : 0 < X := by linarith
  have hl : 0 < Real.log X := Real.log_pos hX
  have hd : 0 < denominator X j :=
    (by positivity : 0 < (Real.log X)^3/96).trans_le (denominator_lower X hX j hj)
  simp_rw [deletionCell_eq_kernel_sum]
  rw [integral_finsetSum _ (fun k _ =>
    (movingKernel_integrable X Y (tripleProduct k) hXp hY).const_mul _)]
  calc
    _ ≤ ∑ k ∈ (coordinates X j).filter (fun k => ¬PositiveSharpCounts.allPrime k),
        (tripleWeight k/denominator X j)*4 := by
      apply Finset.sum_le_sum
      intro k _
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (movingKernel_integral_le X Y (tripleProduct k) hXp hY)
        (div_nonneg (tripleWeight_nonneg k) hd.le)
    _ = _ := by
      unfold PositiveSharpDeletionMass.cellBadMass PositiveSharpDeletionMass.badTripleMass
        PositiveSharpDeletionMass.allPrime PositiveSharpDeletionMass.tripleMass
        coordinates PositiveSharpCounts.allPrime tripleWeight
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem deletion_cell_mean_le (X Y : ℝ) (hX : 1 < X) (hY : 0 < Y)
    (j : ℕ × ℕ) (hj : j ∈ boxes (mesh X))
    (hbad : PositiveSharpDeletionMass.cellBadMass X j ≤
      384*X*Real.log X/Real.sqrt (PositiveSharpDeletionMass.shortestScale X)) :
    (∫ x in Icc X (2*X), deletionCell X j x (x*Y/X))/X ≤
      147456/((Real.log X)^2*Real.sqrt (PositiveSharpDeletionMass.shortestScale X)) := by
  have hXp : 0 < X := by linarith
  have hl : 0 < Real.log X := Real.log_pos hX
  have hs : 0 < Real.sqrt (PositiveSharpDeletionMass.shortestScale X) :=
    Real.sqrt_pos.2 (Real.rpow_pos_of_pos hXp _)
  have hd := denominator_lower X hX j hj
  have hdp : 0 < denominator X j := (by positivity : 0 < (Real.log X)^3/96).trans_le hd
  have hd' : 4/denominator X j ≤ 384/(Real.log X)^3 := by
    apply (div_le_div_iff₀ hdp (pow_pos hl 3)).mpr
    linarith
  apply (div_le_iff₀ hXp).mpr
  calc
    _ ≤ 4/denominator X j*PositiveSharpDeletionMass.cellBadMass X j :=
      deletion_integral_le_mass X Y hX hY j hj
    _ ≤ (384/(Real.log X)^3)*
        (384*X*Real.log X/Real.sqrt (PositiveSharpDeletionMass.shortestScale X)) := by
      exact mul_le_mul hd' hbad (PositiveSharpDeletionMass.cellBadMass_nonneg X j) (by positivity)
    _ = _ := by field_simp; ring

theorem cell_card_normalized_bound (X : ℝ) (hX : 1 < X) (hm : mesh X ≤ 1/1000000) :
    ((boxes (mesh X)).card:ℝ)/(Real.log X)^2 ≤ 1/45 := by
  have hl : 0 < Real.log X := Real.log_pos hX
  have h2 : (1/2:ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at hh
    linarith
  have hmass := (boxes_area_bounds (mesh X) (mesh_pos X hX) hm).2
  have harea : totalArea ≤ (1/180:ℝ) := by rw [total_area_exact]; norm_num
  have hmul := mesh_mul_log X hX
  have hc : 0 ≤ ((boxes (mesh X)).card:ℝ) := Nat.cast_nonneg _
  have ht := mul_le_mul_of_nonneg_right (hmass.trans harea) (sq_nonneg (Real.log X))
  have he : ((boxes (mesh X)).card:ℝ)*(mesh X)^2*(Real.log X)^2=
      ((boxes (mesh X)).card:ℝ)*(Real.log 2)^2 := by rw [← hmul]; ring
  rw [he] at ht
  have hsq : (1/4:ℝ) ≤ (Real.log 2)^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hsq hc
  apply (div_le_iff₀ (pow_pos hl 2)).mpr
  nlinarith

theorem actual_total_deletion_mean_bound :
    ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ X ≥ X0, ∀ Y : ℝ, 0 < Y →
      (∫ x in Icc X (2*X), deletionTotal X x (x*Y/X))/X ≤ 4096/X^((1:ℝ)/12) := by
  obtain ⟨A,hA,hbad⟩ := PositiveSharpDeletionMass.actual_badTripleMass_bound
  refine ⟨max A (Real.exp (1000000*Real.log 2)), hA.trans (le_max_left _ _), ?_⟩
  intro X hX Y hY
  have hXA : A ≤ X := (le_max_left _ _).trans hX
  have hX1 : 1 < X := by linarith [hA.trans hXA]
  have hXp : 0 < X := by linarith
  have hl : 0 < Real.log X := Real.log_pos hX1
  have hs : 0 < Real.sqrt (PositiveSharpDeletionMass.shortestScale X) :=
    Real.sqrt_pos.2 (Real.rpow_pos_of_pos hXp _)
  have hlog : 1000000*Real.log 2 ≤ Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos (1000000*Real.log 2)) ((le_max_right _ _).trans hX)
    simpa only [Real.log_exp] using hh
  have hm : mesh X ≤ 1/1000000 := by
    unfold mesh
    apply (div_le_iff₀ hl).mpr
    linarith
  have hcard := cell_card_normalized_bound X hX1 hm
  have hi (j : ℕ × ℕ) (_hj : j ∈ boxes (mesh X)) :
      IntegrableOn (fun x => deletionCell X j x (x*Y/X)) (Icc X (2*X)) :=
    deletionCell_integrable X Y hXp hY j
  unfold deletionTotal
  rw [integral_finsetSum _ hi, Finset.sum_div]
  calc
    _ ≤ ∑ _j ∈ boxes (mesh X),
        147456/((Real.log X)^2*Real.sqrt (PositiveSharpDeletionMass.shortestScale X)) :=
      Finset.sum_le_sum (fun j hj => deletion_cell_mean_le X Y hX1 hY j hj (hbad X hXA j hj))
    _ = (((boxes (mesh X)).card:ℝ)/(Real.log X)^2*147456)/
        Real.sqrt (PositiveSharpDeletionMass.shortestScale X) := by simp; ring
    _ ≤ ((1/45)*147456)/Real.sqrt (PositiveSharpDeletionMass.shortestScale X) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcard (by norm_num)) hs.le
    _ ≤ 4096/Real.sqrt (PositiveSharpDeletionMass.shortestScale X) :=
      div_le_div_of_nonneg_right (by norm_num) hs.le
    _ = _ := by rw [PositiveSharpDeletionMass.sqrt_shortest X hXp.le]

run_cmd do
  for decl in [``movingSet_measurable, ``window_size_bounds, ``moving_support_subset,
      ``movingKernel_integrable, ``movingKernel_integral_le, ``denominator_lower,
      ``deletionCell_eq_kernel_sum, ``deletionCell_integrable, ``deletionTotal_integrable,
      ``deletion_integral_le_mass,
      ``deletion_cell_mean_le, ``cell_card_normalized_bound, ``actual_total_deletion_mean_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL SHARP MOVING-WINDOW DELETION MEAN <=4096 X^(-1/12); NO PRIME RESIDUAL ESTIMATE"
end PositiveSharpMovingWindow
end
