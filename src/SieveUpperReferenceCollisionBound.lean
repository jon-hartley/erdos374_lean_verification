import SieveRepeatedBandDeletion
import SieveRepeatedBandBudget
import SievePrimeBandMass
import SieveUpperPoolReference

/-! Remove the distinct-band restriction from the actual large-pool upper
selector. All removed signs are controlled by one unsigned collision mass.
The remaining small-prime cutoff is explicit in the final reference. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
open Real SieveBoxedFamily SieveBoxTuples SieveStoppingExpansion SieveUpperPoolReference

namespace SieveUpperReferenceCollisionBound

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
    |reference D s z - SieveUpperBoundaryReference.referenceDistinct D s z| ≤
      primeEuler (D^(s^2))*((SieveBoxLength.cutoff s : ℝ)^2*
        SievePrimeBandMass.eta D s*SieveBoundaryEuler.subsetProduct D s z) :=
  (difference_abs_le D s z hD hs hz).trans
    (mul_le_mul_of_nonneg_left (collisionMass_le D s z hD hs hz) (SieveEulerRatio.euler_pos _).le)

theorem uniformly_small_reference_difference (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ,
        D^(s^2) ≤ z → z ≤ D →
          |reference D s z - SieveUpperBoundaryReference.referenceDistinct D s z| ≤ ε*primeEuler z := by
  obtain ⟨s₀, hs₀, hsHalf, hb⟩ := SieveRepeatedBandBudget.uniformly_small_amplification ε hε
  refine ⟨s₀, hs₀, hsHalf, ?_⟩
  intro s hs hss
  obtain ⟨D₀, hD₀, hbound⟩ := hb s hs hss
  refine ⟨D₀, hD₀, fun D hD z hu hz => ?_⟩
  exact (difference_le_amplification D s z (hD₀.trans_le hD) hs hz).trans
    (hbound D hD z hu hz)

run_cmd do
  for decl in [``collisionMass_le, ``difference_le_amplification,
    ``uniformly_small_reference_difference] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL UPPER REFERENCE COLLISION ERROR UNIFORMLY SMALL"
end SieveUpperReferenceCollisionBound
end
