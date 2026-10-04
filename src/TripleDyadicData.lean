import FourPrimeGlobalPartition
import FourPrimePartitionRemainder

/-! Uniform strict dyadic data for the one-prime / two-prime grouping.
The support hypotheses concern every actual Cartesian pair. Active bins
inherit their upper product bound from actual members, retaining endpoints. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter
open scoped BigOperators

namespace TripleDyadicData
open FourPrimePartition

theorem eventually_half_power (a b : ℝ) (hab : a < b) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧ X ^ a ≤ X ^ b / 2 := by
  filter_upwards [PolynomialLogEnvelope.eventually_constant_bound
    2 (b-a) (by norm_num) (by linarith)] with X hh
  have hXp : 0 < X := by linarith [hh.1]
  refine ⟨hh.1, ?_⟩
  have heq : X ^ (b-a) * X ^ a = X ^ b := by
    rw [← Real.rpow_add hXp]
    congr 1
    ring
  have hm := mul_le_mul_of_nonneg_right hh.2 (Real.rpow_nonneg hXp.le a)
  rw [heq] at hm
  linarith

theorem eventually_data (c : ℝ) (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧ ∀ (S T : Finset ℕ),
      (∀ n ∈ S, 2 ≤ n) → (∀ n ∈ T, 2 ≤ n) →
      (∀ n ∈ S, (n : ℝ) ≤ X) → (∀ n ∈ T, (n : ℝ) ≤ X) →
      (∀ n ∈ S, X ^ (228/1000 : ℝ) ≤ (n : ℝ)) →
      (∀ n ∈ T, X ^ (456/1000 : ℝ) ≤ (n : ℝ)) →
      (∀ m ∈ S, ∀ n ∈ T, (m : ℝ) * n ≤ X ^ (26/35 : ℝ)) →
      let k := FourPrimeGlobalPartition.k X
      let F := family S T 1 1 k k
      (∀ n ∈ S, 1 < n ∧ n ≤ scale 1 (k+1)) ∧
      (∀ n ∈ T, 1 < n ∧ n ≤ scale 1 (k+1)) ∧
      (F.card : ℝ) ≤ X ^ (c/4) ∧
      ∀ ij ∈ F,
        1 ≤ scale 1 ij.1 ∧ 1 ≤ scale 1 ij.2 ∧
        X ^ (227/1000 : ℝ) ≤ (scale 1 ij.1 : ℝ) ∧
        X ^ (455/1000 : ℝ) ≤ (scale 1 ij.2 : ℝ) ∧
        ((scale 1 ij.1 * scale 1 ij.2 : ℕ) : ℝ) ≤ X ^ (26/35 : ℝ) ∧
        (∀ n ∈ block S 1 ij.1, scale 1 ij.1 < n ∧ n ≤ 2 * scale 1 ij.1) ∧
        (∀ n ∈ block T 1 ij.2, scale 1 ij.2 < n ∧ n ≤ 2 * scale 1 ij.2) := by
  filter_upwards [eventually_half_power (227/1000) (228/1000) (by norm_num),
    eventually_half_power (455/1000) (456/1000) (by norm_num),
    FourPrimeGlobalPartition.eventually_all_family_cost (c/2) (by positivity)]
    with X hM hN hcard
  refine ⟨hM.1, ?_⟩
  intro S T hS hT hSX hTX hSlow hTlow hprod
  dsimp only
  refine ⟨FourPrimeGlobalPartition.support_cover X hM.1 S hS hSX,
    FourPrimeGlobalPartition.support_cover X hM.1 T hT hTX, ?_, ?_⟩
  · simpa only [show c/2/2 = c/4 by ring] using hcard.2 S T
  · intro ij hij
    have hmem := Finset.mem_product.mp hij
    have hm : 1 ≤ scale 1 ij.1 := scale_pos 1 ij.1 le_rfl
    have hn : 1 ≤ scale 1 ij.2 := scale_pos 1 ij.2 le_rfl
    refine ⟨hm, hn, ?_, ?_, ?_, block_bounds S 1 ij.1, block_bounds T 1 ij.2⟩
    · exact hM.2.trans (active_scale_lower S 1 _ ij.1 _ hSlow hmem.1)
    · exact hN.2.trans (active_scale_lower T 1 _ ij.2 _ hTlow hmem.2)
    · have hh := family_scale_product_lt S T 1 1 _ _ _ le_rfl le_rfl hprod ij hij
      simpa only [Nat.cast_mul] using hh.le

run_cmd do
  for decl in [``eventually_half_power, ``eventually_data] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "TRIPLE STRICT DYADIC GEOMETRY AND CARDINAL COST PASSED"

end TripleDyadicData
