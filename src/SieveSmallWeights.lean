import SieveRosserSupport
import SievePrimeSubsetEvaluation
import Mathlib.Data.Finset.Sort

/-! Explicit small-prime Rosser weights: the ambient pool contains exactly
the primes strictly below z, and the level is T. For T=D^s and z=D^(s^2)
these are the finite weights used in Iwaniec's Lemma 4 construction.
This module proves their finite support properties, not his main-term estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SieveSmallWeights

def pool (z : ℝ) : Finset ℕ := (Finset.range ⌈z⌉₊).filter Nat.Prime

def primes (z : ℝ) : List ℕ := (pool z).sort (fun p q => q ≤ p)

def primorial (z : ℝ) : ℕ := ∏ p ∈ pool z, p

def support (T z : ℝ) (mode : Bool) : Finset ℕ :=
  SievePrimeSubset.selectedSupport (SieveRosser.selected T mode (primes z))

def weight (T z : ℝ) (mode : Bool) : ℕ → ℝ :=
  SieveRosser.coefficient T mode (primes z)

theorem mem_pool (z : ℝ) (p : ℕ) : p ∈ pool z ↔ p.Prime ∧ (p : ℝ) < z := by
  simp only [pool, Finset.mem_filter, Finset.mem_range, Nat.lt_ceil]
  tauto

theorem primes_toFinset (z : ℝ) : (primes z).toFinset = pool z := by
  simp [primes]

theorem mem_primes (z : ℝ) (p : ℕ) : p ∈ primes z ↔ p.Prime ∧ (p : ℝ) < z := by
  rw [← List.mem_toFinset, primes_toFinset, mem_pool]

theorem primes_nodup (z : ℝ) : (primes z).Nodup := Finset.sort_nodup _ _

theorem primes_descending (z : ℝ) : (primes z).Pairwise (fun p q => q ≤ p) :=
  Finset.pairwise_sort _ _

theorem primes_prime (z : ℝ) : ∀ p ∈ primes z, p.Prime :=
  fun p hp => ((mem_primes z p).mp hp).1

theorem support_positive (T z : ℝ) (mode : Bool) (m : ℕ)
    (hm : m ∈ support T z mode) : 1 ≤ m :=
  SievePrimeSubset.selectedSupport_positive _
    (SieveRosser.selected_primes T mode (primes z) (primes_prime z)) m hm

theorem support_lt (T z : ℝ) (mode : Bool) (hT : 1 < T) (hz : z ≤ T)
    (m : ℕ) (hm : m ∈ support T z mode) : (m : ℝ) < T := by
  obtain ⟨s, hs, rfl⟩ := (SievePrimeSubset.mem_selectedSupport _ m).mp hm
  exact SieveRosser.selected_product_lt T mode (primes z) hT (primes_nodup z)
    (primes_descending z) (fun p hp => (primes_prime z p hp).one_lt.le)
    (fun p hp => (((mem_primes z p).mp hp).2).trans_le hz) s hs

theorem support_dvd_primorial (T z : ℝ) (mode : Bool) (m : ℕ)
    (hm : m ∈ support T z mode) : m ∣ primorial z := by
  obtain ⟨s, hs, rfl⟩ := (SievePrimeSubset.mem_selectedSupport _ m).mp hm
  apply Finset.prod_dvd_prod_of_subset
  simpa only [primes_toFinset] using SieveRosser.selected_subset T mode (primes z) s hs

theorem weight_abs_le_one (T z : ℝ) (mode : Bool) (m : ℕ) :
    |weight T z mode m| ≤ 1 :=
  SieveRosser.coefficient_abs_le_one T mode (primes z) (primes_prime z) m

theorem weight_one (T z : ℝ) (mode : Bool) : weight T z mode 1 = 1 :=
  SieveRosser.coefficient_one T mode (primes z) (primes_prime z)

theorem weight_zero_off_support (T z : ℝ) (mode : Bool) (m : ℕ)
    (hm : m ∉ support T z mode) : weight T z mode m = 0 :=
  SievePrimeSubset.selectedCoefficient_zero_of_not_mem _ m hm

theorem weight_zero_above_level (T z : ℝ) (mode : Bool) (hT : 1 < T) (hz : z ≤ T)
    (m : ℕ) (hm : T ≤ (m : ℝ)) : weight T z mode m = 0 := by
  apply weight_zero_off_support
  intro hmem
  exact (not_lt_of_ge hm) (support_lt T z mode hT hz m hmem)

theorem power_parameters (D s : ℝ) (hD : 1 < D) (hs : 0 < s) (hs1 : s ≤ 1) :
    1 < D ^ s ∧ D ^ (s^2) ≤ D ^ s := by
  refine ⟨Real.one_lt_rpow hD hs, Real.rpow_le_rpow_of_exponent_le hD.le ?_⟩
  nlinarith

/-- Literal error coefficient for a positive even term in the -R convention. -/
def lowerErrorCoefficient (D s : ℝ) (m : ℕ) : ℝ :=
  -weight (D^s) (D^(s^2)) false m

theorem lowerErrorCoefficient_properties (D s : ℝ) (hD : 1 < D)
    (hs : 0 < s) (hs1 : s ≤ 1) (m : ℕ) :
    |lowerErrorCoefficient D s m| ≤ 1 ∧
      (m ∉ support (D^s) (D^(s^2)) false → lowerErrorCoefficient D s m = 0) ∧
      (m ∈ support (D^s) (D^(s^2)) false →
        1 ≤ m ∧ (m : ℝ) < D^s ∧ m ∣ primorial (D^(s^2))) := by
  obtain ⟨hT, hz⟩ := power_parameters D s hD hs hs1
  refine ⟨by simpa [lowerErrorCoefficient] using weight_abs_le_one (D^s) (D^(s^2)) false m, ?_, ?_⟩
  · intro hm
    simp [lowerErrorCoefficient, weight_zero_off_support _ _ _ _ hm]
  · intro hm
    exact ⟨support_positive _ _ _ m hm, support_lt _ _ _ hT hz m hm,
      support_dvd_primorial _ _ _ m hm⟩

run_cmd do
  for decl in [``mem_pool, ``primes_toFinset, ``mem_primes, ``primes_nodup,
      ``primes_descending, ``primes_prime, ``support_positive, ``support_lt,
      ``support_dvd_primorial, ``weight_abs_le_one, ``weight_one,
      ``weight_zero_off_support, ``weight_zero_above_level, ``power_parameters,
      ``lowerErrorCoefficient_properties] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXPLICIT SMALL PRIME WEIGHTS PASSED; BOXING AND MAIN TERM NOT ASSERTED"

end SieveSmallWeights
end
