import PositiveSharpRemainderSupportGeometry
import PositiveSharpRemainderAnalysisCap

/-! The complete literal physical remainder support has positive indices
bounded by X squared. The cofactor prime is retained in that physical index.
Consequently the fixed-s coefficient envelope holds on the entire support. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace PositiveSharpRemainderSupport
open PositiveSharpRemainderAnalysisPhysical PositiveSharpRemainderSupportGeometry
open PositiveSharpBoxedCount PositiveSharpSieveDecomposition
open SieveWeightedCutoffs SieveWeightedScalarBudget
open SieveCappedUpperMainTerms (cappedFourth)

theorem level_le_X (X s : ℝ) (hX : 1≤X) (hs : 0≤s) : level X s≤X := by
  simpa only [level, Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hX (show 1-3*s≤(1:ℝ) by linarith)

theorem upper_support_bounds (X s : ℝ) (P : Finset ℕ) (w : ℝ→ℝ)
    (hX : 1<X) (hs : 0<s) (hsh : s≤1/2)
    (hp : ∀p∈P, 0<p)
    (hg : ∀p∈P, 1<level X s/(p:ℝ) ∧ w p≤level X s/(p:ℝ))
    (m : ℕ) (hm : m∈upperSupport X s P w) : 0<m ∧ (m:ℝ)≤X^2 := by
  obtain ⟨p,hpP,hm⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨hap,hak⟩ := Finset.mem_product.mp ha
  have hap' : a.1=p := Finset.mem_singleton.mp hap
  have hp0 : 0<(p:ℝ) := by exact_mod_cast hp p hpP
  have hp1 : 1≤(p:ℝ) := by exact_mod_cast hp p hpP
  have hgeom := hg p hpP
  have hk0 := SieveUpperBoxWindow.support_positive _ _ _ hgeom.1 hs a.2 hak
  have hk := upper_support_le_square _ _ _ hgeom.1 hs hsh hgeom.2 a.2 hak
  have hD : level X s/(p:ℝ)≤X := by
    apply (div_le_iff₀ hp0).mpr
    exact (level_le_X X s hX.le hs.le).trans (le_mul_of_one_le_right (by linarith) hp1)
  have he : (p:ℝ)*(level X s/(p:ℝ))=level X s := by field_simp
  constructor
  · simpa only [DirichletProductCoefficients.productIndex, hap'] using Nat.mul_pos (hp p hpP) hk0
  · calc
      _ = (p:ℝ)*(a.2:ℝ) := by simp only [DirichletProductCoefficients.productIndex, Nat.cast_mul, hap']
      _ ≤ (p:ℝ)*(level X s/(p:ℝ))^2 := mul_le_mul_of_nonneg_left hk hp0.le
      _ = level X s*(level X s/(p:ℝ)) := by rw [pow_two, ←mul_assoc, he]
      _ ≤ X*X := mul_le_mul (level_le_X X s hX.le hs.le) hD
        (by linarith [hgeom.1]) (by linarith)
      _ = X^2 := (pow_two X).symm

theorem large_support_bounds (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X)
    (m : ℕ) (hm : m∈upperSupport X s (largePrimes X) (cutoffThree X s)) :
    0<m ∧ (m:ℝ)≤X^2 := by
  apply upper_support_bounds X s _ _ hX hs (by linarith)
    (fun p hp => (large_band_bounds X p hp).1.pos) _ m hm
  intro p hp
  have hb := large_band_bounds X p hp
  have hg := three_geometry X s p hX hs.le hs1 hlog hb.2.1 hb.2.2
  have hu := upper_geometry X s p (cutoffThree X s p) hX hs.le hs1 hlog
    (by exact_mod_cast hb.1.one_le) hg.1 hg.2.2
  exact ⟨hu.1,hu.2.1⟩

theorem small_support_bounds (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X)
    (m : ℕ) (hm : m∈upperSupport X s (smallPrimes X s) (cappedFourth X s)) :
    0<m ∧ (m:ℝ)≤X^2 := by
  apply upper_support_bounds X s _ _ hX hs (by linarith)
    (fun p hp => (small_band_bounds X s p hp).1.pos) _ m hm
  intro p hp
  have hb := small_band_bounds X s p hp
  have hg := SieveCappedUpperMainTerms.capped_geometry X s p hX hs.le hs1 hb.2.1 hb.2.2.le
  have hu := upper_geometry X s p (cappedFourth X s p) hX hs.le hs1 hlog
    (by exact_mod_cast hb.1.one_le) hg.1 hg.2.2
  exact ⟨hu.1,hu.2.1⟩

/-- This is the entire support of the exact physical collection, before any
coefficient cancellation. All repeated tuples and overlapping families remain. -/
theorem support_bounds (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X)
    (m : ℕ) (hm : m∈PositiveSharpRemainderAnalysisPhysical.support X s) :
    0<m ∧ (m:ℝ)≤X^2 := by
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hm
  fin_cases i
  · change m∈SieveBoxedWindow.support (level X s) s (X^alpha s) at hi
    have hg := first_geometry X s hX hs.le hs1
    refine ⟨SieveBoxedWindow.support_positive _ _ _ hg.1 hs m hi, ?_⟩
    exact (lower_support_le_square _ _ _ hg.1 hs (by linarith) hg.2.1 m hi).trans
      (pow_le_pow_left₀ (by linarith [hg.1]) (level_le_X X s hX.le hs.le) 2)
  · exact large_support_bounds X s hX hs hs1 hlog m hi
  · exact small_support_bounds X s hX hs hs1 hlog m hi

/-- Fixed s and epsilon are chosen before the scale threshold. There is no
remaining index-range premise on actual support members. -/
theorem eventually_support_coefficient_cap (s ε : ℝ) (hs : 0<s)
    (hs1 : s≤1/1000) (hε : 0<ε) :
    ∀ᶠ X : ℝ in Filter.atTop, 1<X ∧ ∀m∈PositiveSharpRemainderAnalysisPhysical.support X s,
      0<m ∧ (m:ℝ)≤X^2 ∧ |PositiveSharpRemainderAnalysisPhysical.coefficient X s m|≤X^ε := by
  filter_upwards [PositiveSharpRemainderAnalysisCap.eventually_complete_coefficient_cap s ε hε,
    Filter.eventually_gt_atTop (1:ℝ), Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop 1000)]
      with X hcap hX hlog
  refine ⟨hX,?_⟩
  intro m hm
  have hb := support_bounds X s hX hs hs1 hlog m hm
  exact ⟨hb.1,hb.2,hcap.2 m (Nat.ne_of_gt hb.1) hb.2⟩

run_cmd do
  for decl in [``level_le_X, ``upper_support_bounds, ``large_support_bounds,
      ``small_support_bounds, ``support_bounds, ``eventually_support_coefficient_cap] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ENTIRE PHYSICAL SUPPORT AND COMPLETE COEFFICIENT ENVELOPE PASSED"

end PositiveSharpRemainderSupport
