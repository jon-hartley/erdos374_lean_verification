import SieveBoxMass
import SieveBoxedWindow
import SieveStoppingExpansion

/-! The actual boxed main term and its exact nonnegative stopping deficit.
The quantitative fundamental-lemma bound on the stopping sums is still open. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators

namespace SieveModelLoss

def euler (D s : ℝ) : ℝ :=
  SievePrefixLoss.euler (SieveSmallWeights.primes (D^(s^2))) (fun p => (p : ℝ)⁻¹)

def loss (D s : ℝ) (upper : Bool) : ℝ :=
  ((SieveStoppingExpansion.stops (SieveRosser.cubicGate (D^s)) upper 1
    (SieveSmallWeights.primes (D^(s^2)))).map
      (SieveStoppingExpansion.weight (fun p => (p : ℝ)⁻¹))).sum

def ideal (D s z : ℝ) : ℝ :=
  euler D s * (SieveBoxMass.mass true D s z - SieveBoxMass.mass false D s z)

def deficit (D s z : ℝ) : ℝ := ideal D s z - SieveBoxedWindow.mainTerm D s z

theorem euler_pos (D s : ℝ) : 0 < euler D s :=
  SieveReciprocalModel.euler_positive _ (SieveSmallWeights.primes_prime _)

theorem loss_nonneg (D s : ℝ) (upper : Bool) : 0 ≤ loss D s upper := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
  exact SieveStoppingExpansion.small_stop_nonnegative (D^s) (D^(s^2)) upper v hv

theorem small_lower_exact (D s : ℝ) :
    SieveBoxedWindow.smallMass D s false = euler D s - loss D s false :=
  SieveStoppingExpansion.small_lower_mass (D^s) (D^(s^2))

theorem small_upper_exact (D s : ℝ) :
    SieveBoxedWindow.smallMass D s true = euler D s + loss D s true :=
  SieveStoppingExpansion.small_upper_mass (D^s) (D^(s^2))

theorem mainTerm_exact (D s z : ℝ) :
    SieveBoxedWindow.mainTerm D s z =
      ideal D s z - loss D s false * SieveBoxMass.mass true D s z -
        loss D s true * SieveBoxMass.mass false D s z := by
  have hm : SieveBoxedWindow.mainTerm D s z =
      SieveBoxedWindow.smallMass D s false * SieveBoxMass.mass true D s z -
      SieveBoxedWindow.smallMass D s true * SieveBoxMass.mass false D s z := by
    simp [SieveBoxedWindow.mainTerm, SieveBoxMass.mass, SieveBoxMass.reciprocal,
      SieveBoxGrouping.family, one_div]
  rw [hm, small_lower_exact, small_upper_exact, ideal]
  ring

theorem deficit_exact (D s z : ℝ) :
    deficit D s z = loss D s false * SieveBoxMass.mass true D s z +
      loss D s true * SieveBoxMass.mass false D s z := by
  rw [deficit, mainTerm_exact]
  ring

theorem deficit_nonneg (D s z : ℝ) : 0 ≤ deficit D s z := by
  rw [deficit_exact]
  exact add_nonneg
    (mul_nonneg (loss_nonneg D s false) (SieveBoxMass.mass_nonneg true D s z))
    (mul_nonneg (loss_nonneg D s true) (SieveBoxMass.mass_nonneg false D s z))

theorem mainTerm_le_ideal (D s z : ℝ) : SieveBoxedWindow.mainTerm D s z ≤ ideal D s z :=
  sub_nonneg.mp (deficit_nonneg D s z)

theorem deficit_le_max_loss (D s z : ℝ) (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (hband : ∀ i ≤ SieveGeometricGrid.cutoff s, SieveBoxMass.bandMass D s z i ≤ 1/2) :
    deficit D s z ≤ max (loss D s false) (loss D s true) *
      Real.exp (2 * SieveBoxMass.primeMass D s z) := by
  rw [deficit_exact]
  calc
    _ ≤ max (loss D s false) (loss D s true) *
        (SieveBoxMass.mass true D s z + SieveBoxMass.mass false D s z) := by
      rw [mul_add]
      exact add_le_add
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (SieveBoxMass.mass_nonneg true D s z))
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (SieveBoxMass.mass_nonneg false D s z))
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (SieveBoxMass.total_mass_le_exp_of_band_bound D s z hD hs hz hband)
      ((loss_nonneg D s false).trans (le_max_left _ _))

/-- This records exactly where a quantitative fundamental lemma is required:
its relative loss bound is an explicit premise, not a proved analytic input. -/
theorem deficit_le_of_relative_loss (D s z δ : ℝ)
    (hD : 1 < D) (hs : 0 < s) (hz : z ≤ D)
    (hband : ∀ i ≤ SieveGeometricGrid.cutoff s, SieveBoxMass.bandMass D s z i ≤ 1/2)
    (hsmall : ∀ mode, loss D s mode ≤ δ * euler D s) :
    deficit D s z ≤ δ * euler D s * Real.exp (2 * SieveBoxMass.primeMass D s z) :=
  (deficit_le_max_loss D s z hD hs hz hband).trans
    (mul_le_mul_of_nonneg_right (max_le (hsmall false) (hsmall true)) (Real.exp_pos _).le)

#print axioms deficit_le_max_loss
run_cmd do
  for decl in [``euler_pos, ``loss_nonneg, ``small_lower_exact, ``small_upper_exact,
    ``mainTerm_exact, ``deficit_exact, ``deficit_nonneg, ``mainTerm_le_ideal,
    ``deficit_le_max_loss, ``deficit_le_of_relative_loss] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end SieveModelLoss
end
