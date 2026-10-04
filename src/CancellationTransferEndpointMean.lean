import CancellationTransferEndpoints
import PolynomialLogEnvelope

/-! A uniform unconditional L1 bound for the literal source/actual dyadic
endpoint discrepancy. No short-interval prime-distribution hypothesis is used.
The model centering and Mellin/low-frequency transfer are separate issues. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators
namespace CancellationTransferEndpointMean
open PositiveInteriorModel PositiveInteriorCells PositiveInteriorRectangles
open PositiveSharpCounts PositiveSharpMovingWindow PositiveSharpDeletionMass
open CancellationTransferEndpoints

theorem indices_two (X : ℝ) (hX : 1<X) (hm : mesh X≤1/8)
    (j : ℕ×ℕ) (hj : j∈boxes (mesh X)) : 2≤j.1 ∧ 2≤j.2 := by
  have hp := (mesh_pos X hX).le
  have hc := component_bounds _ _ (box_interior (mesh X) (mesh_pos X hX) j hj)
  have hh (m : ℕ) (h : (1/4:ℝ)≤(m:ℝ)*mesh X) : 2≤m := by
    by_contra hn
    have hm1 : m≤1 := by omega
    have hm1r : (m:ℝ)≤1 := by exact_mod_cast hm1
    have hh := mul_le_mul_of_nonneg_right hm1r hp
    nlinarith
  exact ⟨hh j.1 hc.1,hh j.2 hc.2.1⟩

theorem coverBadMass_bound :
    ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ X ≥ X0, ∀ j ∈ boxes (mesh X),
      coverBadMass X j ≤ 384*X*Real.log X/Real.sqrt (shortestScale X) := by
  obtain ⟨Y,hY⟩ := eventually_atTop.mp psi_le_twice_eventually
  obtain ⟨B,hB⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/6)).eventually_ge_atTop (max 1 Y))
  refine ⟨max 2 (max B (Real.exp (8*Real.log 2))), le_max_left _ _, ?_⟩
  intro X hX j hj
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
  have hX1 : 1 < X := by linarith
  have hXB : B ≤ X := (le_max_left _ _).trans ((le_max_right _ _).trans hX)
  have hsmall : max 1 Y ≤ shortestScale X := hB X hXB
  have hlog : 8*Real.log 2 ≤ Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos (8*Real.log 2))
      ((le_max_right _ _).trans ((le_max_right _ _).trans hX))
    simpa only [Real.log_exp] using hh
  have hm : mesh X ≤ 1/8 := by
    unfold mesh
    apply (div_le_iff₀ (Real.log_pos hX1)).mpr
    linarith
  have hs := scales_ge_shortest X hX1 j hj
  have hu := upper_endpoints_le X hX1 hm j hj
  have hp : 1 ≤ scale j.1 := (le_max_left _ _).trans (hsmall.trans hs.1)
  have hr : 1 ≤ scale j.2 := (le_max_left _ _).trans (hsmall.trans hs.2.1)
  have hL : 1 ≤ thirdScale X j := (le_max_left _ _).trans (hsmall.trans hs.2.2)
  have hYp : Y ≤ scale j.1 := (le_max_right _ _).trans (hsmall.trans hs.1)
  have hYr : Y ≤ scale j.2 := (le_max_right _ _).trans (hsmall.trans hs.2.1)
  have hYL : Y ≤ thirdScale X j := (le_max_right _ _).trans (hsmall.trans hs.2.2)
  have hh := badTripleMass_interval_bound 0 (2*scale j.1)
    0 (2*scale j.2) (thirdScale X j/8) (4*thirdScale X j)
    (shortestScale X) (Real.log X) (by linarith) (by linarith) (by linarith)
    (Real.rpow_pos_of_pos (by linarith : 0 < X) _)
    (by linarith [hs.1]) (by linarith [hs.2.1]) (by linarith [hs.2.2])
    (Real.log_le_log (by linarith) hu.1)
    (Real.log_le_log (by linarith) hu.2.1)
    (Real.log_le_log (by linarith) hu.2.2)
    (hY _ (by linarith)) (hY _ (by linarith)) (hY _ (by linarith))
  rw [upper_endpoints_product] at hh
  have he : coverBadMass X j =
      badTripleMass (Finset.Ioc ⌊(0:ℝ)⌋₊ ⌊2*scale j.1⌋₊)
        (Finset.Ioc ⌊(0:ℝ)⌋₊ ⌊2*scale j.2⌋₊)
        (Finset.Ioc ⌊thirdScale X j/8⌋₊ ⌊4*thirdScale X j⌋₊) := by
    simp only [coverBadMass,cover,badTripleMass,Nat.floor_zero,floor_twice_scale]
    rfl
  rw [he]
  convert hh using 1
  ring

theorem endpoint_cell_mean_le (X Y : ℝ) (hX : 1 < X) (hY : 0 < Y)
    (j : ℕ × ℕ) (hj : j ∈ boxes (mesh X)) (hj2 : 2≤j.1 ∧ 2≤j.2)
    (hbad : coverBadMass X j ≤
      384*X*Real.log X/Real.sqrt (PositiveSharpDeletionMass.shortestScale X)) :
    (∫ x in Icc X (2*X), |endpointCell X j x (x*Y/X)|)/X ≤
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
    _ ≤ 4/denominator X j*coverBadMass X j :=
      endpointCell_integral_le X Y hX hY j hj hj2
    _ ≤ (384/(Real.log X)^3)*
        (384*X*Real.log X/Real.sqrt (PositiveSharpDeletionMass.shortestScale X)) := by
      exact mul_le_mul hd' hbad (Finset.sum_nonneg (fun k _ => tripleWeight_nonneg k)) (by positivity)
    _ = _ := by field_simp; ring

theorem actual_endpoint_mean_bound :
    ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ X ≥ X0, ∀ Y : ℝ, 0 < Y →
      (∫ x in Icc X (2*X), endpointTotal X x (x*Y/X))/X ≤ 4096/X^((1:ℝ)/12) := by
  obtain ⟨A,hA,hbad⟩ := coverBadMass_bound
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
      IntegrableOn (fun x => |endpointCell X j x (x*Y/X)|) (Icc X (2*X)) :=
    endpointCell_abs_integrable X Y hXp hY j
  unfold endpointTotal
  rw [integral_finsetSum _ hi, Finset.sum_div]
  calc
    _ ≤ ∑ _j ∈ boxes (mesh X),
        147456/((Real.log X)^2*Real.sqrt (PositiveSharpDeletionMass.shortestScale X)) :=
      Finset.sum_le_sum (fun j hj => endpoint_cell_mean_le X Y hX1 hY j hj
        (indices_two X hX1 (by linarith) j hj) (hbad X hXA j hj))
    _ = (((boxes (mesh X)).card:ℝ)/(Real.log X)^2*147456)/
        Real.sqrt (PositiveSharpDeletionMass.shortestScale X) := by simp; ring
    _ ≤ ((1/45)*147456)/Real.sqrt (PositiveSharpDeletionMass.shortestScale X) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcard (by norm_num)) hs.le
    _ ≤ 4096/Real.sqrt (PositiveSharpDeletionMass.shortestScale X) :=
      div_le_div_of_nonneg_right (by norm_num) hs.le
    _ = _ := by rw [PositiveSharpDeletionMass.sqrt_shortest X hXp.le]

theorem eventually_endpoint_mean_log (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ ∀ Y : ℝ, 0<Y →
      (∫ x in Icc X (2*X), endpointTotal X x (x*Y/X))/X≤1/(Real.log X)^A := by
  obtain ⟨X0,hX0,hb⟩ := actual_endpoint_mean_bound
  filter_upwards [eventually_ge_atTop X0,
    PolynomialLogEnvelope.eventually_bound 4096 A (1/12) (by norm_num) (by norm_num)]
      with X hXX he
  have hX : 1<X := by linarith
  have hl : 0<Real.log X := Real.log_pos hX
  have hp : 0<X^((1:ℝ)/12) := Real.rpow_pos_of_pos (by linarith) _
  have hlog : 4096*(Real.log X)^A≤X^((1:ℝ)/12) := by
    apply le_trans _ he.2
    gcongr
    linarith
  refine ⟨hX,?_⟩
  intro Y hY
  exact (hb X hXX Y hY).trans ((div_le_div_iff₀ hp (pow_pos hl A)).mpr (by simpa using hlog))

run_cmd do
  for decl in [``indices_two,``coverBadMass_bound,``endpoint_cell_mean_le,
      ``actual_endpoint_mean_bound,``eventually_endpoint_mean_log] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "LITERAL DYADIC ENDPOINT NORMALIZED L1 <=4096 X^(-1/12), UNIFORMLY ALL Y>0"
end CancellationTransferEndpointMean
end
