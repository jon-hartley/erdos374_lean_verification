import SieveBoxCollisions
import SieveEulerRatio
import SieveBoxMassTwo
import SieveCollisionDecay
import SieveModelLoss

/-! Vanishing same-band error on the actual Euler-product scale.
This controls one genuine component of the boxed main-term comparison;
first-failure sums and cubic-boundary discrepancies are still separate. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators Topology
open Filter
namespace SieveNormalizedCollisions
open SieveBoxMass SieveBoxCollisions SieveStoppingExpansion

def normalizedMass (positive : Bool) (D s z : ℝ) : ℝ :=
  (primeEuler (D^(s^2)) / primeEuler z) * collisionMass positive D s z

def distinctMass (positive : Bool) (D s z : ℝ) : ℝ :=
  ∑ t ∈ (SieveBoxGrouping.family positive D s z).filter
    (fun t => (SieveBoxedFamily.indices D s t).Nodup), reciprocal t

def strictIdeal (D s z : ℝ) : ℝ :=
  primeEuler (D^(s^2)) * (mass true D s z - distinctMass false D s z)

theorem mass_sub_distinctMass (positive : Bool) (D s z : ℝ) :
    mass positive D s z - distinctMass positive D s z = collisionMass positive D s z := by
  classical
  have h := Finset.sum_filter_add_sum_filter_not (SieveBoxGrouping.family positive D s z)
    (fun t => (SieveBoxedFamily.indices D s t).Nodup) reciprocal
  change distinctMass positive D s z + collisionMass positive D s z = mass positive D s z at h
  linarith

theorem strictIdeal_sub_ideal (D s z : ℝ) :
    strictIdeal D s z - SieveModelLoss.ideal D s z =
      primeEuler (D^(s^2)) * collisionMass false D s z := by
  have h := mass_sub_distinctMass false D s z
  change primeEuler (D^(s^2)) * (mass true D s z - distinctMass false D s z) -
    primeEuler (D^(s^2)) * (mass true D s z - mass false D s z) = _
  rw [show primeEuler (D^(s^2)) * (mass true D s z - distinctMass false D s z) -
      primeEuler (D^(s^2)) * (mass true D s z - mass false D s z) =
      primeEuler (D^(s^2)) * (mass false D s z - distinctMass false D s z) by ring, h]

/-- Both remaining small-prime losses retain their actual signs and weights. -/
theorem mainTerm_strict_exact (D s z : ℝ) :
    SieveBoxedWindow.mainTerm D s z = strictIdeal D s z -
      primeEuler (D^(s^2)) * collisionMass false D s z -
      SieveModelLoss.loss D s false * mass true D s z -
      SieveModelLoss.loss D s true * mass false D s z := by
  have h := strictIdeal_sub_ideal D s z
  rw [SieveModelLoss.mainTerm_exact]
  linarith

theorem normalizedMass_nonneg (positive : Bool) (D s z : ℝ) :
    0 ≤ normalizedMass positive D s z :=
  mul_nonneg (SieveEulerRatio.ratio_nonneg D s z) (collisionMass_nonneg positive D s z)

theorem normalizedMass_le (positive : Bool) (D s z η : ℝ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D) (hu : D^(s^2) ≤ z)
    (h17 : 17 ≤ D^(s^2))
    (hband : ∀ i ≤ SieveGeometricGrid.cutoff s, bandMass D s z i ≤ 1/17)
    (hη : ∀ i ≤ SieveGeometricGrid.cutoff s, bandMass D s z i ≤ η) :
    normalizedMass positive D s z ≤
      (η * primeMass D s z) * Real.exp ((17/8) * primeMass D s z) := by
  unfold normalizedMass
  calc
    _ ≤ Real.exp ((17/16)*primeMass D s z) *
        ((η * primeMass D s z) * Real.exp ((17/16)*primeMass D s z)) :=
      mul_le_mul (SieveEulerRatio.ratio_le_exp D s z hu h17)
        (collisionMass_le positive D s z η hD hs hz hband hη)
        (collisionMass_nonneg positive D s z) (Real.exp_pos _).le
    _ = _ := by
      rw [show Real.exp ((17/16)*primeMass D s z) *
          ((η * primeMass D s z) * Real.exp ((17/16)*primeMass D s z)) =
          (η * primeMass D s z) *
          (Real.exp ((17/16)*primeMass D s z) * Real.exp ((17/16)*primeMass D s z)) by ring,
        ← Real.exp_add]
      congr 2
      ring

/-- The large-D threshold precedes both the actual cutoff and parity choice. -/
theorem eventually_normalizedMass (s : ℝ) (hs : 0 < s) (hsHalf : s ≤ 1/2) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ,
      D^(s^2) ≤ z → z ≤ D → ∀ positive : Bool,
      normalizedMass positive D s z ≤ SieveCollisionDecay.normalizedError s := by
  obtain ⟨D₀, hD₀, hbound⟩ := SieveBoxMassTwo.small_parameter_bounds_two s hs hsHalf
  refine ⟨D₀, hD₀, fun D hD z hu hz positive => ?_⟩
  obtain ⟨h17, hband, hη, hprime, _⟩ := hbound D hD z hz
  have hS : 0 ≤ primeMass D s z :=
    Finset.sum_nonneg (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p))
  have hη0 : 0 ≤ 3*s^9 := by positivity
  have hmain := normalizedMass_le positive D s z (3*s^9) (hD₀.trans_le hD) hs hz hu h17
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

theorem euler_scaled_le (positive : Bool) (D s z ε : ℝ)
    (h : normalizedMass positive D s z ≤ ε) :
    primeEuler (D^(s^2)) * collisionMass positive D s z ≤ ε * primeEuler z := by
  apply (div_le_iff₀ (SieveEulerRatio.euler_pos z)).mp
  simpa only [normalizedMass, div_mul_eq_mul_div] using h

/-- A genuinely vanishing error relative to `V(z)`, uniformly in the actual
prime cutoff. No unproved reciprocal-mass or distribution premise remains. -/
theorem uniformly_small_collision (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1/2 ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ z : ℝ,
        D^(s^2) ≤ z → z ≤ D → ∀ positive : Bool,
        primeEuler (D^(s^2)) * collisionMass positive D s z ≤ ε * primeEuler z := by
  obtain ⟨s₁, hs₁, herror⟩ := SieveCollisionDecay.normalizedError_small ε hε
  refine ⟨min s₁ (1/2), lt_min hs₁ (by norm_num), min_le_right _ _, ?_⟩
  intro s hs hss
  have hsHalf : s ≤ 1/2 := (hss.trans_le (min_le_right _ _)).le
  obtain ⟨D₀, hD₀, hmass⟩ := eventually_normalizedMass s hs hsHalf
  refine ⟨D₀, hD₀, fun D hD z hu hz positive => ?_⟩
  apply euler_scaled_le positive D s z ε
  exact (hmass D hD z hu hz positive).trans
    (herror s hs (hss.trans_le (min_le_left _ _))).le

#print axioms uniformly_small_collision
run_cmd do
  for decl in [``mass_sub_distinctMass, ``strictIdeal_sub_ideal, ``mainTerm_strict_exact,
    ``normalizedMass_nonneg, ``normalizedMass_le,
    ``eventually_normalizedMass, ``euler_scaled_le, ``uniformly_small_collision] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end SieveNormalizedCollisions
end
