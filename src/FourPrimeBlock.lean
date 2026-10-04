import FourPrimeScaleBudget
import FourPrimePartitionRemainder
import FactoredDivisorSourceWindow
import FourPrimeGlobalData

/-! Application of the divisor estimate to two independent finite supports.
Global doubling bins preserve the full small-divisor range. The left
coefficient may contain every ordered four-factor representation.
No sieve inequality is assumed or concluded here. -/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set

namespace FourPrimeBlock
open FourPrimeScaleBudget FourPrimePartition

theorem eventually_bound (s : ℝ) (hs : 0 < s) (hs1 : s < 1 / 100) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      ∀ (S T : Finset ℕ) (a b : ℕ → ℝ),
        (∀ m ∈ S, 2 ≤ m) → (∀ n ∈ T, 2 ≤ n) →
        (∀ n ∈ T, X ^ lowerExponent s ≤ (n : ℝ)) →
        (∀ n ∈ T, (n : ℝ) ≤ X ^ (1 / 6 : ℝ)) →
        (∀ m ∈ S, ∀ n ∈ T, (m : ℝ) * n ≤ X ^ (1 - 2 * s)) →
        (∀ m ∈ S, |a m| ≤ (m.divisors.card : ℝ) ^ 4) →
        (∀ n ∈ T, |b n| ≤ 1) →
        let Y := FactoredDivisorVariableWindow.sourceWindow s X
        (1 / X) * (∫ x in Icc X (2 * X),
          HarmanDivisorWindow.remainder
            (FactoredDivisorWeights.support S T)
            (FactoredDivisorWeights.coefficient S T a b)
            (x - x * (Y / X)) x ^ 2) ≤ Y ^ 2 * X ^ (-c) := by
  have hb := lowerExponent_pos s hs hs1
  obtain ⟨c, hc, hfamily⟩ := FactoredDivisorVariableWindow.eventually_source_bound
    (ι := ℕ × ℕ) (lowerExponent s / 2) (s / 2) (s / 2)
    (lowerExponent s / 2) s
    (by positivity) (by positivity) (by positivity) (by positivity) hs hs1
  refine ⟨c, hc, ?_⟩
  filter_upwards [hfamily, eventually_divisor_fourth c hc,
    eventual_lower_bin_budget s hs hs1,
    FourPrimeGlobalPartition.eventually_family_cost c hc] with X hf hdiv hbin hcost
  refine ⟨hdiv.1, ?_⟩
  intro S T a b hS hT hTlow hTupper hprod ha hbweight
  dsimp only
  have hX : 1 ≤ X := hdiv.1
  have hXp : 0 < X := by linarith
  by_cases hTempty : T = ∅
  · subst T
    simp only [FactoredDivisorWeights.support, HarmanDivisorWindow.productSupport,
      Finset.product_empty, Finset.image_empty, HarmanDivisorWindow.remainder,
      HarmanDivisorWindow.divisorCount, HarmanDivisorWindow.reciprocalMass,
      Finset.sum_empty, mul_zero, sub_self, zero_pow (by decide : 2 ≠ 0),
      integral_zero]
    positivity
  have hTne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hTempty
  obtain ⟨hcoverS, hcoverT, hcard, hdata⟩ := global_data X s c hX hs hc
    hdiv.2 hbin.2 hcost.2 S T a b hTne hS hT hTlow hTupper hprod ha hbweight
  let k := FourPrimeGlobalPartition.k X
  let u : ℕ := 1
  let v : ℕ := 1
  let F := family S T u v k k
  let M := fun ij : ℕ × ℕ => scale u ij.1
  let N := fun ij : ℕ × ℕ => scale v ij.2
  let sm := fun ij : ℕ × ℕ => block S u ij.1
  let sn := fun ij : ℕ × ℕ => block T v ij.2
  have hh := hf.2 F M N sm sn (fun _ => a) (fun _ => b) hcard hdata
  -- Rewrite the exact family sum, preserving repeated product indices.
  simpa only [F, M, N, sm, sn,
    FourPrimePartition.remainder_family_eq S T u v k k a b hcoverS hcoverT] using hh

end FourPrimeBlock

#print axioms FourPrimeBlock.eventually_bound
run_cmd do
  for ax in (← Lean.collectAxioms ``FourPrimeBlock.eventually_bound) do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "FOUR PRIME BLOCK PASSED"
