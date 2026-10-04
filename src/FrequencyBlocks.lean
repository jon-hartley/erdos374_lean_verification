import SeparatedFrequencyRows

/-!
Exact finite partition of a real interval into frequency blocks. The
cardinality bound includes the final partial block and all endpoints.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace FrequencyBlocks

def block (r : Finset ℝ) (a H : ℝ) (k : ℕ) : Finset ℝ := by
  classical
  exact r.filter (fun t => ⌊(t - a) / H⌋₊ = k)

theorem block_subset (r : Finset ℝ) (a H : ℝ) (k : ℕ) :
    block r a H k ⊆ r := Finset.filter_subset _ _

theorem block_diameter (r : Finset ℝ) (a H : ℝ) (k : ℕ) (hH : 0 < H)
    (hlower : ∀ t ∈ r, a ≤ t) :
    ∀ x ∈ block r a H k, ∀ y ∈ block r a H k, |x - y| ≤ H := by
  intro x hx y hy
  have hx' := Finset.mem_filter.mp hx
  have hy' := Finset.mem_filter.mp hy
  have hxlo := Nat.floor_le (div_nonneg (sub_nonneg.mpr (hlower x hx'.1)) hH.le)
  have hylo := Nat.floor_le (div_nonneg (sub_nonneg.mpr (hlower y hy'.1)) hH.le)
  have hxhi := Nat.lt_floor_add_one ((x - a) / H)
  have hyhi := Nat.lt_floor_add_one ((y - a) / H)
  rw [hx'.2] at hxlo hxhi
  rw [hy'.2] at hylo hyhi
  have hxl := (le_div_iff₀ hH).mp hxlo
  have hyl := (le_div_iff₀ hH).mp hylo
  have hxu := (div_lt_iff₀ hH).mp hxhi
  have hyu := (div_lt_iff₀ hH).mp hyhi
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

theorem card_bound (r : Finset ℝ) (a T H C : ℝ)
    (hT : 0 ≤ T) (hH : 0 < H) (hC : 0 ≤ C)
    (hrange : ∀ t ∈ r, a ≤ t ∧ t ≤ a + T)
    (hblock : ∀ k : ℕ, ((block r a H k).card : ℝ) ≤ C) :
    (r.card : ℝ) ≤ (T / H + 1) * C := by
  classical
  let count := ⌊T / H⌋₊ + 1
  have hmaps : (r : Set ℝ).MapsTo (fun t => ⌊(t - a) / H⌋₊) (Finset.range count) := by
    intro t ht
    apply Finset.mem_range.mpr
    have hh := Nat.floor_mono
      (div_le_div_of_nonneg_right (show t - a ≤ T by linarith [(hrange t ht).2]) hH.le)
    dsimp [count]
    omega
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  change r.card = ∑ k ∈ Finset.range count, (block r a H k).card at hcard
  have hcount : (count : ℝ) ≤ T / H + 1 := by
    dsimp [count]
    push_cast
    linarith [Nat.floor_le (div_nonneg hT hH.le)]
  calc
    _ = ∑ k ∈ Finset.range count, ((block r a H k).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ _k ∈ Finset.range count, C := Finset.sum_le_sum (fun k _ => hblock k)
    _ = (count : ℝ) * C := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount hC

end FrequencyBlocks

#print axioms FrequencyBlocks.card_bound
run_cmd do
  for target in [``FrequencyBlocks.block_diameter, ``FrequencyBlocks.card_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "FREQUENCY BLOCKS PASSED"
