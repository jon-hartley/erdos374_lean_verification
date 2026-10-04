import SievePrimeSubsetEvaluation
import SievePrefixLoss
import HarmanDivisorWindow

/-! The exact reciprocal main term of the actual finite selectors.
The Euler product is positive, but the lower selector's mass is not asserted
positive: its nonnegative stopping loss still needs a quantitative estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators

namespace SieveReciprocalModel

def mass (gate : ℕ → ℕ → Prop) (mode : Bool) (d : ℕ) (ps : List ℕ) : ℝ :=
  HarmanDivisorWindow.reciprocalMass
    (SievePrimeSubset.selectedSupport (SievePrefix.selected gate mode d ps))
    (SievePrimeSubset.selectedCoefficient (SievePrefix.selected gate mode d ps))

theorem collected_reciprocal (A : Finset (Finset ℕ)) :
    HarmanDivisorWindow.reciprocalMass (SievePrimeSubset.selectedSupport A)
        (SievePrimeSubset.selectedCoefficient A) =
      ∑ s ∈ A, (-1 : ℝ)^s.card * ∏ p ∈ s, (p : ℝ)⁻¹ := by
  simp only [HarmanDivisorWindow.reciprocalMass, div_eq_mul_inv]
  rw [SievePrimeSubset.sum_selectedCoefficient_kernel]
  apply Finset.sum_congr rfl
  intro s hs
  simp [SievePrimeSubset.subsetProduct, Nat.cast_prod, Finset.prod_inv_distrib]

theorem mass_eq_value (gate : ℕ → ℕ → Prop) (mode : Bool) (d : ℕ) (ps : List ℕ) :
    mass gate mode d ps = SievePrefix.value gate mode d ps (fun p => (p : ℝ)⁻¹) :=
  collected_reciprocal _

theorem reciprocal_in_unit_interval (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime) :
    ∀ p ∈ ps, 0 ≤ (p : ℝ)⁻¹ ∧ (p : ℝ)⁻¹ ≤ 1 := by
  intro p hps
  constructor
  · positivity
  · apply inv_le_one_of_one_le₀
    exact_mod_cast (hp p hps).one_lt.le

theorem euler_positive (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime) :
    0 < SievePrefixLoss.euler ps (fun p => (p : ℝ)⁻¹) := by
  apply Finset.prod_pos
  intro p hps
  apply sub_pos.mpr
  apply inv_lt_one_of_one_lt₀
  exact_mod_cast (hp p (List.mem_toFinset.mp hps)).one_lt

/-- These inequality directions alone give no positive lower sieve main term. -/
theorem mass_bounds (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ)
    (hnd : ps.Nodup) (hp : ∀ p ∈ ps, p.Prime) :
    mass gate false d ps ≤ SievePrefixLoss.euler ps (fun p => (p : ℝ)⁻¹) ∧
      SievePrefixLoss.euler ps (fun p => (p : ℝ)⁻¹) ≤ mass gate true d ps := by
  rw [mass_eq_value, mass_eq_value]
  exact SievePrefix.value_bounds gate d ps _ hnd (reciprocal_in_unit_interval ps hp)

theorem lower_mass_exact (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ) :
    mass gate false d ps = SievePrefixLoss.euler ps (fun p => (p : ℝ)⁻¹) -
      SievePrefixLoss.lower gate d ps (fun p => (p : ℝ)⁻¹) := by
  rw [mass_eq_value]
  unfold SievePrefixLoss.lower
  ring

theorem upper_mass_exact (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ) :
    mass gate true d ps = SievePrefixLoss.euler ps (fun p => (p : ℝ)⁻¹) +
      SievePrefixLoss.upper gate d ps (fun p => (p : ℝ)⁻¹) := by
  rw [mass_eq_value]
  unfold SievePrefixLoss.upper
  ring

theorem loss_nonnegative (gate : ℕ → ℕ → Prop) (d : ℕ) (ps : List ℕ)
    (hnd : ps.Nodup) (hp : ∀ p ∈ ps, p.Prime) :
    0 ≤ SievePrefixLoss.lower gate d ps (fun p => (p : ℝ)⁻¹) ∧
      0 ≤ SievePrefixLoss.upper gate d ps (fun p => (p : ℝ)⁻¹) :=
  SievePrefixLoss.nonnegative gate d ps _ hnd (reciprocal_in_unit_interval ps hp)

run_cmd do
  for decl in [``collected_reciprocal, ``mass_eq_value, ``reciprocal_in_unit_interval,
      ``euler_positive, ``mass_bounds, ``lower_mass_exact, ``upper_mass_exact,
      ``loss_nonnegative] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "SIEVE RECIPROCAL MODEL IDENTITIES PASSED; QUANTITATIVE LOWER ESTIMATE OPEN"

end SieveReciprocalModel
end
