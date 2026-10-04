import SieveUpperOuterCollisions
import SieveEulerRatio
import SieveBoxMassTwo
import SieveCollisionDecay

/-! The actual repeated-band outer upper mass is uniformly negligible
relative to V(z). The bound retains every repeated-coordinate tuple. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators Topology
open Filter
namespace SieveUpperNormalizedOuterCollisions
open SieveBoxMass SieveUpperOuterCollisions SieveStoppingExpansion

def normalizedMass (D s z : ℝ) : ℝ :=
  (primeEuler (D^(s^2))/primeEuler z)*collisionMass D s z

theorem normalizedMass_nonneg (D s z : ℝ) :
    0 ≤ normalizedMass D s z :=
  mul_nonneg (SieveEulerRatio.ratio_nonneg D s z) (collisionMass_nonneg D s z)

theorem normalizedMass_le (D s z η : ℝ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) (hu : D^(s^2) ≤ z)
    (h17 : 17 ≤ D^(s^2))
    (hband : ∀ i ≤ SieveGeometricGrid.cutoff s, bandMass D s z i ≤ 1/17)
    (hη : ∀ i ≤ SieveGeometricGrid.cutoff s, bandMass D s z i ≤ η) :
    normalizedMass D s z ≤
      (η * primeMass D s z) * Real.exp ((17/8) * primeMass D s z) := by
  unfold normalizedMass
  calc
    _ ≤ Real.exp ((17/16)*primeMass D s z) *
        ((η * primeMass D s z) * Real.exp ((17/16)*primeMass D s z)) :=
      mul_le_mul (SieveEulerRatio.ratio_le_exp D s z hu h17)
        (collisionMass_le D s z η hD hs hz hband hη)
        (collisionMass_nonneg D s z) (Real.exp_pos _).le
    _ = _ := by
      rw [show Real.exp ((17/16)*primeMass D s z) *
          ((η * primeMass D s z) * Real.exp ((17/16)*primeMass D s z)) =
          (η * primeMass D s z) *
          (Real.exp ((17/16)*primeMass D s z) * Real.exp ((17/16)*primeMass D s z)) by ring,
        ← Real.exp_add]
      congr 2
      ring

/-- The large-D threshold precedes the actual upper cutoff. -/
theorem eventually_normalizedMass (s : ℝ) (hs : 0 < s) (hsHalf : s ≤ 1/2) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ,
      D^(s^2) ≤ z → z ≤ D →
      normalizedMass D s z ≤ SieveCollisionDecay.normalizedError s := by
  obtain ⟨D₀, hD₀, hbound⟩ := SieveBoxMassTwo.small_parameter_bounds_two s hs hsHalf
  refine ⟨D₀, hD₀, fun D hD z hu hz => ?_⟩
  obtain ⟨h17, hband, hη, hprime, _⟩ := hbound D hD z hz
  have hS : 0 ≤ primeMass D s z :=
    Finset.sum_nonneg (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p))
  have hη0 : 0 ≤ 3*s^9 := by positivity
  have hmain := normalizedMass_le D s z (3*s^9) (hD₀.trans_le hD) hs hz hu h17
    (fun i _ => hband i) (fun i _ => hη i)
  apply hmain.trans
  calc
    _ ≤ ((3*s^9) * (2*Real.log (1/s^2)+1)) *
        Real.exp ((17/8)*(2*Real.log (1/s^2)+1)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hprime hη0)
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hprime (by norm_num)))
        (Real.exp_pos _).le (mul_nonneg hη0 (hS.trans hprime))
    _ = _ := by
      rw [show (17/8 : ℝ)*(2*Real.log (1/s^2)+1) =
        (17/8 : ℝ) + Real.log (1/s^2)*(17/4 : ℝ) by ring,
        Real.exp_add, Real.exp_mul, Real.exp_log (by positivity)]
      unfold SieveCollisionDecay.normalizedError
      ring

theorem euler_scaled_le (D s z ε : ℝ)
    (h : normalizedMass D s z ≤ ε) :
    primeEuler (D^(s^2)) * collisionMass D s z ≤ ε * primeEuler z := by
  apply (div_le_iff₀ (SieveEulerRatio.euler_pos z)).mp
  simpa only [normalizedMass, div_mul_eq_mul_div] using h

/-- A genuinely vanishing error relative to `V(z)`, uniformly in the actual
prime cutoff. No unproved reciprocal-mass or distribution premise remains. -/
theorem uniformly_small_collision (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ,
        D^(s^2) ≤ z → z ≤ D →
        primeEuler (D^(s^2)) * collisionMass D s z ≤ ε * primeEuler z := by
  obtain ⟨s₁, hs₁, herror⟩ := SieveCollisionDecay.normalizedError_small ε hε
  refine ⟨min s₁ (1/2), lt_min hs₁ (by norm_num), min_le_right _ _, ?_⟩
  intro s hs hss
  have hsHalf : s ≤ 1/2 := (hss.trans_le (min_le_right _ _)).le
  obtain ⟨D₀, hD₀, hmass⟩ := eventually_normalizedMass s hs hsHalf
  refine ⟨D₀, hD₀, fun D hD z hu hz => ?_⟩
  apply euler_scaled_le D s z ε
  exact (hmass D hD z hu hz).trans
    (herror s hs (hss.trans_le (min_le_left _ _))).le
theorem uniformly_small_ideal_gap (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ,
        D^(s^2) ≤ z → z ≤ D →
          SieveUpperModelLoss.ideal D s z-SieveUpperBoundaryReference.strictIdeal D s z ≤
            ε*primeEuler z := by
  obtain ⟨s₀, hs₀, hsHalf, hb⟩ := uniformly_small_collision ε hε
  refine ⟨s₀, hs₀, hsHalf, ?_⟩
  intro s hs hss
  obtain ⟨D₀, hD₀, hbound⟩ := hb s hs hss
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD z hu hz
  rw [ideal_sub_strictIdeal]
  exact hbound D hD z hu hz

run_cmd do
  for decl in [``normalizedMass_nonneg, ``normalizedMass_le,
      ``eventually_normalizedMass, ``euler_scaled_le, ``uniformly_small_collision,
      ``uniformly_small_ideal_gap] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL OUTER UPPER COLLISION ERROR VANISHES RELATIVE TO V"
end SieveUpperNormalizedOuterCollisions
end
