import SieveAppendComparison
import SievePrimeListSplit
import SievePoolReference
import SieveReciprocalModel

/-! Exact one-sided removal of the lower prime cutoff. The full lower
selector is below the Euler-weighted large-pool lower selector. The upper
comparison uses its own upper large-pool selector. Only the ordering of
the prime cutoffs is required; no positivity of a lower value is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open SieveStoppingExpansion

namespace SieveFullCutoffTransfer

def fullLower (D z : ℝ) : ℝ :=
  SievePrefix.value (SieveRosser.cubicGate D) false 1
    (SieveSmallWeights.primes z) (fun p => (p : ℝ)⁻¹)

def fullUpper (D z : ℝ) : ℝ :=
  SievePrefix.value (SieveRosser.cubicGate D) true 1
    (SieveSmallWeights.primes z) (fun p => (p : ℝ)⁻¹)

def lowerLarge (D s z : ℝ) : ℝ :=
  SievePrefix.value (SieveRosser.cubicGate D) false 1
    (SieveBoxedFamily.primes D s z) (fun p => (p : ℝ)⁻¹)

def upperLarge (D s z : ℝ) : ℝ :=
  SievePrefix.value (SieveRosser.cubicGate D) true 1
    (SieveBoxedFamily.primes D s z) (fun p => (p : ℝ)⁻¹)

theorem value_eq_signed_reciprocal (D : ℝ) (upper : Bool) (ps : List ℕ) :
    SievePrefix.value (SieveRosser.cubicGate D) upper 1 ps (fun p => (p : ℝ)⁻¹) =
      ∑ A ∈ SieveRosser.selected D upper ps,
        (-1 : ℝ)^A.card * (SievePrimeSubset.subsetProduct A : ℝ)⁻¹ := by
  simp only [SievePrefix.value, SievePrefix.term, SieveRosser.selected,
    SievePrimeSubset.subsetProduct, Nat.cast_prod, Finset.prod_inv_distrib]

theorem fullLower_eq_mass (D z : ℝ) :
    fullLower D z = SieveReciprocalModel.mass (SieveRosser.cubicGate D) false 1
      (SieveSmallWeights.primes z) :=
  (SieveReciprocalModel.mass_eq_value _ _ _ _).symm

theorem fullUpper_eq_mass (D z : ℝ) :
    fullUpper D z = SieveReciprocalModel.mass (SieveRosser.cubicGate D) true 1
      (SieveSmallWeights.primes z) :=
  (SieveReciprocalModel.mass_eq_value _ _ _ _).symm

theorem reference_eq_euler_mul_lowerLarge (D s z : ℝ) :
    SievePoolReference.reference D s z = primeEuler (D^(s^2))*lowerLarge D s z := by
  rw [lowerLarge, value_eq_signed_reciprocal]
  rfl

/-- The two selector states retain their opposite, exact append directions. -/
theorem cutoff_bounds (D s z : ℝ) (hu : D^(s^2) ≤ z) :
    fullLower D z ≤ primeEuler (D^(s^2))*lowerLarge D s z ∧
      primeEuler (D^(s^2))*upperLarge D s z ≤ fullUpper D z := by
  have hsplit := SievePrimeListSplit.primes_split D s z hu
  have hb : ∀ p ∈ SieveBoxedFamily.primes D s z ++ SieveSmallWeights.primes (D^(s^2)),
      0 ≤ (p : ℝ)⁻¹ ∧ (p : ℝ)⁻¹ ≤ 1 := by
    intro p hp
    rw [← hsplit] at hp
    exact SievePrimeListSplit.reciprocal_bounds z p hp
  have h := SieveAppendComparison.value_append_bounds (SieveRosser.cubicGate D) 1
    (SieveBoxedFamily.primes D s z) (SieveSmallWeights.primes (D^(s^2)))
    (fun p => (p : ℝ)⁻¹) (SievePrimeListSplit.append_nodup D s z) hb
  simpa only [← hsplit, fullLower, fullUpper, lowerLarge, upperLarge, primeEuler] using h

theorem fullLower_le_reference (D s z : ℝ) (hu : D^(s^2) ≤ z) :
    fullLower D z ≤ SievePoolReference.reference D s z := by
  rw [reference_eq_euler_mul_lowerLarge]
  exact (cutoff_bounds D s z hu).1

theorem euler_mul_upperLarge_le_fullUpper (D s z : ℝ) (hu : D^(s^2) ≤ z) :
    primeEuler (D^(s^2))*upperLarge D s z ≤ fullUpper D z :=
  (cutoff_bounds D s z hu).2

run_cmd do
  for decl in [``value_eq_signed_reciprocal, ``fullLower_eq_mass,
    ``fullUpper_eq_mass, ``reference_eq_euler_mul_lowerLarge, ``cutoff_bounds,
    ``fullLower_le_reference, ``euler_mul_upperLarge_le_fullUpper] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXACT FULL-PRIME LOWER AND UPPER CUTOFF TRANSFER PASSED"

end SieveFullCutoffTransfer
end
