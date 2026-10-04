import SieveRepeatedBandDeletion
import SieveRepeatedBandBudget
import SievePrimeBandMass
import SievePoolReference
import SieveCubicBoundaryComparison

/-! Remove the distinct-band restriction from the actual large-pool lower
selector. All removed signs are controlled by one unsigned collision mass.
The remaining small-prime cutoff is explicit in the final reference. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
open Real SieveBoxedFamily SieveBoxTuples SieveStoppingExpansion SievePoolReference

namespace SieveReferenceCollisionBound

theorem collisionMass_le (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) :
    collisionMass D s z ≤ (SieveBoxLength.cutoff s : ℝ)^2 *
      SievePrimeBandMass.eta D s*SieveBoundaryEuler.subsetProduct D s z := by
  rw [collisionMass_eq_tupleMass]
  apply SieveRepeatedBandDeletion.reciprocal_mass_le_square
    (collisionTuples D s z) (pool D s z) (fun p => boxIndex D s (p:ℝ))
    (SieveBoxLength.cutoff s) (SievePrimeBandMass.eta D s)
  · intro t ht
    exact (collisionTuples_properties D s z hD hs t ht).1
  · intro t ht
    exact (collisionTuples_properties D s z hD hs t ht).2.1
  · intro t ht
    exact (collisionTuples_properties D s z hD hs t ht).2.2.1
  · intro t ht
    have hp := collisionTuples_properties D s z hD hs t ht
    exact descending_box_indices D s hD hs t (hp.1.imp (fun h => h.le))
      (range_of_pool D s z hz t hp.2.1)
  · intro t ht
    exact (collisionTuples_properties D s z hD hs t ht).2.2.2
  · intro S hS i hi
    exact SievePrimeBandMass.common_band_bound D s z S i hD hs hz
      (fun p hp => ⟨hS hp, hi p hp⟩)

theorem difference_le_amplification (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) :
    |reference D s z - SieveBoundaryReference.referenceDistinct D s z| ≤
      primeEuler (D^(s^2))*((SieveBoxLength.cutoff s : ℝ)^2*
        SievePrimeBandMass.eta D s*SieveBoundaryEuler.subsetProduct D s z) :=
  (difference_abs_le D s z hD hs hz).trans
    (mul_le_mul_of_nonneg_left (collisionMass_le D s z hD hs hz) (SieveEulerRatio.euler_pos _).le)

theorem uniformly_small_reference_difference (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ,
        D^(s^2) ≤ z → z ≤ D →
          |reference D s z - SieveBoundaryReference.referenceDistinct D s z| ≤ ε*primeEuler z := by
  obtain ⟨s₀, hs₀, hsHalf, hb⟩ := SieveRepeatedBandBudget.uniformly_small_amplification ε hε
  refine ⟨s₀, hs₀, hsHalf, ?_⟩
  intro s hs hss
  obtain ⟨D₀, hD₀, hbound⟩ := hb s hs hss
  refine ⟨D₀, hD₀, fun D hD z hu hz => ?_⟩
  exact (difference_le_amplification D s z (hD₀.trans_le hD) hs hz).trans
    (hbound D hD z hu hz)

/-- The actual boxed main term approximates the ordinary lower selector on
the complete large-prime pool, with no distinct-band filter. -/
theorem uniformly_approximate_pool_reference (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ,
        D^(s^2) ≤ z → z ≤ D →
          |SieveBoxedWindow.mainTerm D s z-reference D s z| ≤ ε*primeEuler z := by
  obtain ⟨sC, hsC, hsCHalf, hc⟩ := uniformly_small_reference_difference (ε/2) (by linarith)
  obtain ⟨sM, hsM, _, hm⟩ :=
    SieveCubicBoundaryComparison.uniformly_approximate_reference (ε/2) (by linarith)
  refine ⟨min sC sM, lt_min hsC hsM, (min_le_left _ _).trans hsCHalf, ?_⟩
  intro s hs hss
  obtain ⟨DC, hDC, hcD⟩ := hc s hs (hss.trans_le (min_le_left _ _)).le
  obtain ⟨DM, hDM, hmD⟩ := hm s hs (hss.trans_le (min_le_right _ _))
  refine ⟨max DC DM, hDC.trans_le (le_max_left _ _), ?_⟩
  intro D hD z hu hz
  have hC := hcD D ((le_max_left _ _).trans hD) z hu hz
  have hM := hmD D ((le_max_right _ _).trans hD) z hu hz
  have hδ : 0 ≤ (ε/2)*primeEuler z := mul_nonneg (by linarith) (SieveEulerRatio.euler_pos z).le
  have hMabs : |SieveBoxedWindow.mainTerm D s z-SieveBoundaryReference.referenceDistinct D s z|
      ≤ (ε/2)*primeEuler z := by
    apply abs_le.mpr
    constructor <;> linarith
  have hCabs : |SieveBoundaryReference.referenceDistinct D s z-reference D s z|
      ≤ (ε/2)*primeEuler z := by
    rw [abs_sub_comm]
    exact hC
  calc
    _ ≤ |SieveBoxedWindow.mainTerm D s z-SieveBoundaryReference.referenceDistinct D s z|+
        |SieveBoundaryReference.referenceDistinct D s z-reference D s z| := abs_sub_le _ _ _
    _ ≤ (ε/2)*primeEuler z+(ε/2)*primeEuler z := add_le_add hMabs hCabs
    _ = ε*primeEuler z := by ring

run_cmd do
  for decl in [``collisionMass_le, ``difference_le_amplification,
    ``uniformly_small_reference_difference, ``uniformly_approximate_pool_reference] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "DISTINCT-BAND RESTRICTION REMOVED; ACTUAL MAIN TERM APPROXIMATES FULL LARGE-POOL SELECTOR"
end SieveReferenceCollisionBound
end
