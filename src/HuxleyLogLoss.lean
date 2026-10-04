import LocalLargeValues
import FrequencyBlocks

/-!
An unconditional large-values count with the Huxley V^(-6) term and
explicit logarithmic losses. HuxleyLogLoss is a new project namespace.
The proof uses the proved dyadic kernel, absorbs on short frequency
blocks, then sums the exact finite partition.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators

namespace HuxleyLogLoss
open Erdos374.HarmanAnalytic151MeanSquare

theorem count_bound (N lo hi : ℕ) (coeff : ℕ → ℂ)
    (r : Finset ℝ) (a T E V : ℝ)
    (hN : 1 ≤ N) (hlo : N ≤ lo) (hhi : hi ≤ 2 * N)
    (hT : 0 ≤ T) (hE : 0 < E) (hV : 0 < V)
    (henergy : (∑ n ∈ Finset.Ioc lo hi, ‖coeff n‖ ^ 2) ≤ E)
    (hrange : ∀ t ∈ r, a ≤ t ∧ t ≤ a + T)
    (hsep : ∀ x ∈ r, ∀ y ∈ r, x ≠ y → 1 ≤ |x - y|)
    (hlarge : ∀ t ∈ r, V ≤ ‖exponentialSum151 (Finset.Ioc lo hi)
      coeff (fun n => Real.log n) t‖) :
    (r.card : ℝ) ≤ 258 * N * (1 + Real.log (T + 1)) *
      (E / V ^ 2 + 1024 ^ 2 * T * E ^ 3 *
        (1 + Real.log ((N : ℝ) + 1)) / V ^ 6) := by
  have hGN : 0 < 1 + Real.log ((N : ℝ) + 1) := by
    have hh := Real.log_nonneg (show 1 ≤ (N : ℝ) + 1 by
      linarith [Nat.cast_nonneg (α := ℝ) N])
    linarith
  have hGT : 0 < 1 + Real.log (T + 1) := by
    have hh := Real.log_nonneg (show 1 ≤ T + 1 by linarith)
    linarith
  let H := (V ^ 2 / (1024 * E)) ^ 2 / (1 + Real.log ((N : ℝ) + 1))
  have hH : 0 < H := by dsimp [H]; positivity
  have habsorb :
      1024 * E * Real.sqrt (H * (1 + Real.log ((N : ℝ) + 1))) ≤ V ^ 2 := by
    have hprod : H * (1 + Real.log ((N : ℝ) + 1)) = (V ^ 2 / (1024 * E)) ^ 2 := by
      dsimp [H]
      field_simp
    rw [hprod, Real.sqrt_sq (by positivity)]
    exact le_of_eq (by field_simp)
  let C := 258 * N * (1 + Real.log (T + 1)) * E / V ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hdiamT : ∀ x ∈ r, ∀ y ∈ r, |x - y| ≤ T := by
    intro x hx y hy
    exact abs_le.mpr ⟨by linarith [(hrange x hx).1, (hrange y hy).2],
      by linarith [(hrange y hy).1, (hrange x hx).2]⟩
  have hblock (k : ℕ) : ((FrequencyBlocks.block r a H k).card : ℝ) ≤ C := by
    have hsub := FrequencyBlocks.block_subset r a H k
    exact LocalLargeValues.count_bound N lo hi coeff (FrequencyBlocks.block r a H k)
      T H E V hN hlo hhi hT hH.le hE.le hV henergy
      (fun x hx y hy hne => hsep x (hsub hx) y (hsub hy) hne)
      (fun x hx y hy => hdiamT x (hsub hx) y (hsub hy))
      (FrequencyBlocks.block_diameter r a H k hH (fun t ht => (hrange t ht).1))
      (fun t ht => hlarge t (hsub ht)) habsorb
  calc
    _ ≤ (T / H + 1) * C := FrequencyBlocks.card_bound r a T H C
      hT hH hC hrange hblock
    _ = _ := by
      dsimp [H, C]
      field_simp
      ring

end HuxleyLogLoss

#print axioms HuxleyLogLoss.count_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``HuxleyLogLoss.count_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "HUXLEY LOG LOSS PASSED"
