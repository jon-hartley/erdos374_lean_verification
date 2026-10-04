import SeparatedCoreDiagonalWork

/-! Exact removal of the now-controlled diagonal. The remaining target
is a signed off-diagonal correlation with both centering terms retained. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace SeparatedCoreOffDiagonalWork
open SeparatedCoreGlobalPerronWork SeparatedCoreCorrelationWork SeparatedCoreDiagonalWork
open MovingWindowCorrelationWork PositiveSharpPowerWindow

def offDiagonalCentered (X s Y : ℝ) : ℝ :=
  (∑ p∈(nearPairs (physicalSupport X) Y).filter (fun p => p.1≠p.2),
    physicalCoefficient X s p.1 * physicalCoefficient X s p.2 * overlap X (Y/X) p.1 p.2) -
    2*(Y/X)*mainMass X s*(∑ n∈physicalSupport X,
      physicalCoefficient X s n*firstMoment X (Y/X) n) +
        ((Y/X)*mainMass X s)^2*((7/3 : ℝ)*X^3)

theorem energy_split (X s Y : ℝ) (hY : 0<Y) :
    correlationEnergy X s Y = diagonal X s Y + offDiagonalCentered X s Y := by
  have hdiag : (nearPairs (physicalSupport X) Y).filter (fun p => p.1=p.2) =
      (physicalSupport X).diag := by
    ext p
    simp only [nearPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_diag]
    constructor
    · rintro ⟨⟨⟨h1,h2⟩,hg⟩,he⟩
      exact ⟨h1,he⟩
    · rintro ⟨h1,he⟩
      refine ⟨⟨⟨h1,by simpa [← he] using h1⟩,?_⟩,he⟩
      rw [he, sub_self, abs_zero]
      linarith
  have hh := Finset.sum_filter_add_sum_filter_not (nearPairs (physicalSupport X) Y)
    (fun p => p.1=p.2)
    (fun p => physicalCoefficient X s p.1*physicalCoefficient X s p.2*overlap X (Y/X) p.1 p.2)
  rw [hdiag] at hh
  have hd : (∑ p∈(physicalSupport X).diag,
      physicalCoefficient X s p.1*physicalCoefficient X s p.2*overlap X (Y/X) p.1 p.2) =
      diagonal X s Y := by
    simp only [Finset.diag, Finset.sum_map, Function.Embedding.coeFn_mk, Function.diag]
    simp only [SeparatedCoreDiagonalWork.diagonal, pow_two]
  rw [hd] at hh
  unfold correlationEnergy energy offDiagonalCentered
  rw [← hh]
  ring

/-- A sufficient remaining arithmetic estimate, stated directly for the
whole core. The off-diagonal hypothesis itself is still open. -/
theorem eventually_core_absolute_of_offDiagonal (s C : ℝ) (hs : 0<s) (hs1 : s≤1/1000)
    (hC : 0≤C)
    (hoff : ∀ᶠ X : ℝ in atTop,
      let Y := halfWidth X (101/1000)
      (1/X)*offDiagonalCentered X s Y≤C*Y^2/(Real.log X)^4) :
    ∀ᶠ X : ℝ in atTop,
      let Y := halfWidth X (101/1000)
      (1/X)*(∫ x in Icc X (2*X), |LongPairCloseDistinctMeanWork.separatedRemainder
        X s (x-x*(Y/X)) x|) ≤ Real.sqrt (C+1)*Y/(Real.log X)^2 := by
  filter_upwards [hoff,eventually_diagonal_log s 4 hs hs1,
    halfWidth_eventually (101/1000) (by norm_num)] with X ho hd hY
  dsimp only at ho hd ⊢
  let Y := halfWidth X (101/1000)
  have hXp : 0<X := by linarith [hd.1]
  have hl : 0<Real.log X := Real.log_pos hd.1
  have hYlt : Y<X := by linarith [hY.2]
  have hE : (1/X)*correlationEnergy X s Y≤(C+1)*Y^2/(Real.log X)^4 := by
    rw [energy_split X s Y hY.1, mul_add]
    exact (add_le_add hd.2.2 ho).trans_eq (by ring)
  let B := Real.sqrt (C+1)*Y/(Real.log X)^2
  have hB : 0<B := div_pos
    (mul_pos (Real.sqrt_pos.mpr (by linarith : 0<C+1)) hY.1) (sq_pos_of_pos hl)
  have he : B^2=(C+1)*Y^2/(Real.log X)^4 := by
    dsimp [B]
    rw [div_pow, mul_pow, Real.sq_sqrt (by linarith : 0≤C+1)]
    ring
  have he' : correlationEnergy X s Y≤X*B^2 := by
    rw [← he] at hE
    have hh := mul_le_mul_of_nonneg_left hE hXp.le
    have hx : X*((1/X)*correlationEnergy X s Y)=correlationEnergy X s Y := by field_simp
    rwa [hx] at hh
  exact absolute_mean_of_energy X s Y B hd.1 hs hs1 hd.2.1 hY.1.le hYlt hB he'

theorem eventually_rest_of_offDiagonal (s C : ℝ) (hs : 0<s) (hs1 : s≤1/1000)
    (hC : 0≤C)
    (hoff : ∀ᶠ X : ℝ in atTop,
      let Y := halfWidth X (101/1000)
      (1/X)*offDiagonalCentered X s Y≤C*Y^2/(Real.log X)^4) :
    ∀ᶠ X : ℝ in atTop,
      let Y := halfWidth X (101/1000)
      ShortSingletonClosure.restNegativeMean X s Y≤(8+Real.sqrt (C+1))*Y/(Real.log X)^2 := by
  filter_upwards [eventually_core_absolute_of_offDiagonal s C hs hs1 hC hoff,
    RestSeparatedCoreReductionWork.eventually_rest_mean_le_separatedCore s 2 hs hs1,
    eventually_gt_atTop (1:ℝ)] with X hc hr hX
  dsimp only at hc hr ⊢
  let Y := halfWidth X (101/1000)
  have hi := LongPairRepeatedCoreMeanWork.source_moving_integrable
    (LongPairCloseDistinctMeanWork.separatedSource X s) X s Y
  have hn : RestSeparatedCoreReductionWork.separatedCoreNegativeMean X s Y ≤
      (1/X)*(∫ x in Icc X (2*X), |LongPairCloseDistinctMeanWork.separatedRemainder
        X s (x-x*(Y/X)) x|) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0≤1/X)
    apply setIntegral_mono_on hi.neg_part hi.abs measurableSet_Icc
    intro x hx
    exact max_le (neg_le_abs _) (abs_nonneg _)
  exact (hr.trans (add_le_add le_rfl (hn.trans hc))).trans_eq (by ring)

#print axioms energy_split
#print axioms eventually_rest_of_offDiagonal
run_cmd do
  for decl in [``energy_split, ``eventually_core_absolute_of_offDiagonal,
      ``eventually_rest_of_offDiagonal] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end SeparatedCoreOffDiagonalWork
