import Mathlib.Analysis.PSeries
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open Finset

namespace SieveCollisionBounds

/-- Literal reciprocal mass of a finite pool of natural numbers. -/
def mass (P : Finset ℕ) : ℝ := ∑ p ∈ P, (p : ℝ)⁻¹

/-- Reciprocal mass of ordered pairs, retaining the diagonal. -/
def pairMass (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ P, ((p : ℝ) * (q : ℝ))⁻¹

/-- Reciprocal mass of ordered distinct pairs. -/
def distinctMass (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ P.erase p, ((p : ℝ) * (q : ℝ))⁻¹

def diagonalMass (P : Finset ℕ) : ℝ := ∑ p ∈ P, ((p : ℝ)^2)⁻¹

theorem mass_nonneg (P : Finset ℕ) : 0 ≤ mass P := by
  exact sum_nonneg (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p))

theorem diagonalMass_nonneg (P : Finset ℕ) : 0 ≤ diagonalMass P := by
  exact sum_nonneg (fun p _ => inv_nonneg.mpr (sq_nonneg (p : ℝ)))

theorem pairMass_eq_sq (P : Finset ℕ) : pairMass P = mass P ^ 2 := by
  simp only [pairMass, mass, mul_inv, ← mul_sum, ← sum_mul, pow_two]

theorem distinct_add_diagonal (P : Finset ℕ) :
    distinctMass P + diagonalMass P = pairMass P := by
  unfold distinctMass diagonalMass pairMass
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  simpa only [pow_two] using
    sum_erase_add P (fun q : ℕ => ((p : ℝ) * (q : ℝ))⁻¹) hp

/-- Exact loss from removing repeated primes, with all ordered representations retained. -/
theorem sq_mass_sub_distinct (P : Finset ℕ) :
    mass P ^ 2 - distinctMass P = diagonalMass P := by
  have h := distinct_add_diagonal P
  rw [pairMass_eq_sq] at h
  linarith

/-- A finite pool above a real cutoff has reciprocal-square mass at most
`1/(u-1)`. This all-integer bound needs no prime distribution hypothesis. -/
theorem diagonalMass_le (P : Finset ℕ) (u : ℝ) (hu : 1 < u)
    (hp : ∀ p ∈ P, u ≤ (p : ℝ)) : diagonalMass P ≤ 1 / (u - 1) := by
  let k : ℕ := ⌈u⌉₊ - 1
  let n : ℕ := max k (P.sup id)
  have hc : 2 ≤ ⌈u⌉₊ := Nat.add_one_le_ceil_iff.mpr (by simpa using hu)
  have hk : k ≠ 0 := by dsimp [k]; omega
  have hkn : k ≤ n := le_max_left _ _
  have hsub : P ⊆ Ioc k n := by
    intro p hmem
    have hcp : ⌈u⌉₊ ≤ p := Nat.ceil_le.mpr (hp p hmem)
    have hsup : p ≤ P.sup id := Finset.le_sup (f := id) hmem
    have hpn : p ≤ n := hsup.trans (le_max_right _ _)
    exact mem_Ioc.mpr ⟨by dsimp [k]; omega, hpn⟩
  have hkcast : (k : ℝ) = (⌈u⌉₊ : ℝ) - 1 := by
    dsimp [k]
    rw [Nat.cast_sub (by omega : 1 ≤ ⌈u⌉₊), Nat.cast_one]
  have hku : u - 1 ≤ (k : ℝ) := by rw [hkcast]; linarith [Nat.le_ceil u]
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  calc
    diagonalMass P ≤ ∑ p ∈ Ioc k n, ((p : ℝ)^2)⁻¹ := by
      exact sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    _ ≤ (k : ℝ)⁻¹ - (n : ℝ)⁻¹ := sum_Ioc_inv_sq_le_sub hk hkn
    _ ≤ (k : ℝ)⁻¹ := sub_le_self _ (by positivity)
    _ ≤ 1 / (u - 1) := by
      rw [← one_div]
      exact one_div_le_one_div_of_le (by linarith) hku

theorem distinct_discrepancy_bounds (P : Finset ℕ) (u : ℝ) (hu : 1 < u)
    (hp : ∀ p ∈ P, u ≤ (p : ℝ)) :
    0 ≤ mass P ^ 2 - distinctMass P ∧
      mass P ^ 2 - distinctMass P ≤ 1 / (u - 1) := by
  rw [sq_mass_sub_distinct]
  exact ⟨diagonalMass_nonneg P, diagonalMass_le P u hu hp⟩

theorem distinct_discrepancy_abs_le (P : Finset ℕ) (u : ℝ) (hu : 1 < u)
    (hp : ∀ p ∈ P, u ≤ (p : ℝ)) :
    |mass P ^ 2 - distinctMass P| ≤ 1 / (u - 1) := by
  obtain ⟨hn, hb⟩ := distinct_discrepancy_bounds P u hu hp
  rwa [abs_of_nonneg hn]

/-- A separate same-band estimate: it counts every ordered pair in each band,
including unequal primes. The upper bound on each actual band mass is explicit. -/
theorem same_band_pair_mass_le {ι : Type*} (I : Finset ι)
    (band : ι → Finset ℕ) (η : ℝ) (hη : ∀ i ∈ I, mass (band i) ≤ η) :
    (∑ i ∈ I, pairMass (band i)) ≤ η * ∑ i ∈ I, mass (band i) := by
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  rw [pairMass_eq_sq, pow_two]
  exact mul_le_mul_of_nonneg_right (hη i hi) (mass_nonneg (band i))

#print axioms diagonalMass_le
#print axioms distinct_discrepancy_abs_le
run_cmd do
  for decl in [``mass_nonneg, ``diagonalMass_nonneg, ``pairMass_eq_sq,
      ``distinct_add_diagonal, ``sq_mass_sub_distinct, ``diagonalMass_le,
      ``distinct_discrepancy_bounds, ``distinct_discrepancy_abs_le,
      ``same_band_pair_mass_le] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "SIEVE COLLISION BOUNDS PASSED; standard axioms only"

end SieveCollisionBounds
end
