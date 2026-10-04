import SieveUpperBoundaryReference
import SieveUpperCubicLocalization
import SieveCubicStripMass
import SieveBoundaryEuler

/-! The two actual upper boxed cubic boundary complements have uniformly
vanishing normalized mass. Repeated-band collisions and small-prime stopping
errors are separate contributions, not assumptions of this result. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open Real SieveStoppingExpansion SieveUpperBoundaryReference
namespace SieveUpperBoundaryComparison

theorem inner_width (s : ℝ) (hs : 0 < s) :
    1-1/SieveGeometricGrid.ratio s ≤ s^9 := by
  have hx : 0 ≤ s^9 := by positivity
  have hq : 0 < 1+s^9 := by positivity
  unfold SieveGeometricGrid.ratio
  have hh : 1-1/(1+s^9) = s^9/(1+s^9) := by field_simp; ring
  rw [hh]
  exact (div_le_iff₀ hq).mpr (by nlinarith)

theorem inner_mass_le (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) :
    tupleMass (innerOmissions D s z) ≤ (SieveBoxLength.cutoff s : ℝ)*
      SieveThinPrimeInterval.delta D s*SieveBoundaryEuler.subsetProduct D s z := by
  apply SieveCubicStripMass.cubic_strip_mass_le D s z
    (1/SieveGeometricGrid.ratio s) 1 (innerOmissions D s z) (SieveBoxLength.cutoff s)
    hD hs (inner_width s hs)
  · intro t ht
    exact reference_strict false D s z hD hs hz t (Finset.mem_sdiff.mp ht).1
  · intro t ht
    exact (innerOmissions_properties D s z t ht).1
  · intro t ht
    exact ((mem_refOdd D s z t).mp (Finset.mem_sdiff.mp ht).1).1
  · intro t ht
    obtain ⟨hp, he, hi, ha, hn⟩ := innerOmissions_properties D s z t ht
    obtain ⟨i, hi', _, hg⟩ := SieveUpperCubicLocalization.inner_omission D s z t hD hs hz hp he hi ha hn
    exact ⟨i, hi', by simpa only [Real.rpow_one] using hg⟩

theorem outer_mass_le (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) :
    tupleMass (outerExcess D s z) ≤ (SieveBoxLength.cutoff s : ℝ)*
      SieveThinPrimeInterval.delta D s*SieveBoundaryEuler.subsetProduct D s z := by
  apply SieveCubicStripMass.cubic_strip_mass_le D s z
    1 (SieveGeometricGrid.ratio s) (outerExcess D s z) (SieveBoxLength.cutoff s)
    hD hs (by simp [SieveGeometricGrid.ratio])
  · intro t ht
    exact outerDistinct_strict D s z hD hs hz t (Finset.mem_sdiff.mp ht).1
  · intro t ht
    exact (outerExcess_properties D s z t ht).1
  · intro t ht
    have ho := (Finset.mem_filter.mp (Finset.mem_sdiff.mp ht).1).1
    exact ((SieveBoxedFamily.mem_boundedTuples _ _ _).mp (Finset.mem_filter.mp ho).1).1
  · intro t ht
    obtain ⟨hp, ho, _, hn⟩ := outerExcess_properties D s z t ht
    obtain ⟨i, hi, _, hg⟩ := SieveUpperCubicLocalization.outer_excess D s z t hD hs hz hp ho hn
    exact ⟨i, hi, by simpa only [Real.rpow_one] using hg⟩

theorem gap_le_amplification (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) :
    strictIdeal D s z-referenceDistinct D s z ≤
      primeEuler (D^(s^2)) * (2*(SieveBoxLength.cutoff s : ℝ)*
        SieveThinPrimeInterval.delta D s*SieveBoundaryEuler.subsetProduct D s z) := by
  rw [strictIdeal_sub_referenceDistinct D s z hD hs hz]
  apply mul_le_mul_of_nonneg_left _ (SieveEulerRatio.euler_pos _).le
  have hh := add_le_add (inner_mass_le D s z hD hs hz) (outer_mass_le D s z hD hs hz)
  nlinarith [hh]

theorem gap_le_budget (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hsHalf : s ≤ 1/2) (hu : D^(s^2) ≤ z) (hz : z ≤ D)
    (h2 : 2 ≤ D^(s^2))
    (hK : PrimeEulerDimensionOne.errorConstant ≤ log (D^(s^2))) :
    strictIdeal D s z-referenceDistinct D s z ≤
      SieveBoundaryBudget.budget D s*primeEuler z :=
  (gap_le_amplification D s z hD hs hz).trans
    (SieveBoundaryEuler.euler_amplification D s z hD hs hsHalf hu hz h2 hK)

theorem uniformly_small_boundary_gap (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ,
        D^(s^2) ≤ z → z ≤ D →
          strictIdeal D s z-referenceDistinct D s z ≤ ε*primeEuler z := by
  obtain ⟨s₀, hs₀, hsHalf, hb⟩ := SieveBoundaryEuler.uniformly_small_amplification ε hε
  refine ⟨s₀, hs₀, hsHalf, ?_⟩
  intro s hs hss
  obtain ⟨D₀, hD₀, hbound⟩ := hb s hs hss
  refine ⟨D₀, hD₀, fun D hD z hu hz => ?_⟩
  exact (gap_le_amplification D s z (hD₀.trans_le hD) hs hz).trans (hbound D hD z hu hz)

run_cmd do
  for decl in [``inner_width, ``inner_mass_le, ``outer_mass_le, ``gap_le_amplification,
      ``gap_le_budget, ``uniformly_small_boundary_gap] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL UPPER CUBIC BOUNDARY GAP IS UNIFORMLY SMALL RELATIVE TO V"
end SieveUpperBoundaryComparison
end
