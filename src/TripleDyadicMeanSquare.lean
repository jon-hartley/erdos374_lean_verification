import TripleFlatContourMeanSquare
import TripleDyadicData
import TripleDyadicWeights

/-! The flat contour estimate summed over the exact finite dyadic partition.
Only geometric support bounds and arbitrarily small pointwise powers remain;
the per-block energies, signed convolution caps and partition cost are proved. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace TripleDyadicMeanSquare
open FourPrimePartition

theorem eventually_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
        ∀ (S T : Finset ℕ) (a b : ℕ → ℝ) (Y : ℝ),
          (∀ n ∈ S, 2 ≤ n) → (∀ n ∈ T, 2 ≤ n) →
          (∀ n ∈ S, (n : ℝ) ≤ X) → (∀ n ∈ T, (n : ℝ) ≤ X) →
          (∀ n ∈ S, X ^ (228/1000 : ℝ) ≤ (n : ℝ)) →
          (∀ n ∈ T, X ^ (456/1000 : ℝ) ≤ (n : ℝ)) →
          (∀ m ∈ S, ∀ n ∈ T, (m : ℝ) * n ≤ X ^ (26/35 : ℝ)) →
          (∀ n ∈ S, |a n| ≤ X ^ δ) → (∀ n ∈ T, |b n| ≤ X ^ δ) →
          X ^ (1009/10000 : ℝ) ≤ Y → Y ≤ X/2 →
          (1/X) * (∫ x in Icc X (2*X),
            HarmanDivisorWindow.remainder (FactoredDivisorWeights.support S T)
              (FactoredDivisorWeights.coefficient S T a b)
              (x-x*(Y/X)) x ^ 2) ≤ Y^2 * X^(-c) := by
  obtain ⟨c, hc, ε, hε, hblock⟩ := TripleFlatContourMeanSquare.eventually_bound
  let β := TripleFlatContourMeanSquare.coefficientExponent
  have hβ : 0 < β := TripleFlatContourMeanSquare.coefficientExponent_pos
  let δ := min (ε/2) (β/8)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδε : 2*δ ≤ ε := by have := min_le_left (ε/2) (β/8); dsimp [δ]; linarith
  have hδβ : δ ≤ β/8 := min_le_right _ _
  refine ⟨c/2, by positivity, δ, hδ, ?_⟩
  filter_upwards [hblock, TripleDyadicData.eventually_data c hc,
    TripleDyadicWeights.eventually_coefficient_cap β hβ] with X hb hd hcap
  refine ⟨hd.1, ?_⟩
  intro S T a b Y hS hT hSX hTX hSlow hTlow hprod ha hbw hY hYhalf
  obtain ⟨hcoverS,hcoverT,hcard,hdata⟩ := hd.2 S T hS hT hSX hTX hSlow hTlow hprod
  let k := FourPrimeGlobalPartition.k X
  let F := family S T 1 1 k k
  let supports := fun ij : ℕ × ℕ =>
    FactoredDivisorWeights.support (block S 1 ij.1) (block T 1 ij.2)
  let weights := fun ij : ℕ × ℕ =>
    FactoredDivisorWeights.coefficient (block S 1 ij.1) (block T 1 ij.2) a b
  have hXp : 0 < X := by linarith [hd.1]
  have hY0 : 0 ≤ Y := (Real.rpow_nonneg hXp.le _).trans hY
  have hmean : ∀ ij ∈ F,
      (1/X) * (∫ x in Icc X (2*X), HarmanDivisorWindow.remainder
        (supports ij) (weights ij) (x-x*(Y/X)) x ^ 2) ≤ Y^2 * X^(-c) := by
    intro ij hij
    obtain ⟨hM,hN,hMlow,hNlow,hMN,hsm,hsn⟩ := hdata ij hij
    have ham : ∀ n ∈ block S 1 ij.1, |a n| ≤ X ^ δ := by
      intro n hn
      exact ha n ((mem_block S 1 ij.1 n).mp hn).1
    have han : ∀ n ∈ block T 1 ij.2, |b n| ≤ X ^ δ := by
      intro n hn
      exact hbw n ((mem_block T 1 ij.2 n).mp hn).1
    have hMNX : ((scale 1 ij.1 * scale 1 ij.2 : ℕ) : ℝ) ≤ X := hMN.trans (by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hd.1
        (by norm_num : (26/35 : ℝ) ≤ 1))
    have hweights := hcap.2 (scale 1 ij.1) (scale 1 ij.2)
      (block S 1 ij.1) (block T 1 ij.2) a b hN hMNX hsm hsn
      (fun n hn => (ham n hn).trans (Real.rpow_le_rpow_of_exponent_le hd.1 hδβ))
      (fun n hn => (han n hn).trans (Real.rpow_le_rpow_of_exponent_le hd.1 hδβ))
    apply hb.2 (scale 1 ij.1) (scale 1 ij.2)
      (block S 1 ij.1) (block T 1 ij.2) a b Y
    · exact hMlow
    · simpa only [TripleFlatParameters.pairExponent,
        show (455/1000 : ℝ) = 91/200 by norm_num] using hNlow
    · exact hMN
    · exact hY
    · exact hYhalf
    · exact hsm
    · exact hsn
    · exact TripleDyadicWeights.energy X ε δ _ _ a hd.1 hδε hsm ham
    · exact TripleDyadicWeights.energy X ε δ _ _ b hd.1 hδε hsn han
    · exact hweights
  have hh := FiniteDivisorFamily.normalized_power_bound F supports weights
    X Y c hXp hY0 (by linarith) hcard hmean
  simpa only [F,supports,weights,
    remainder_family_eq S T 1 1 k k a b hcoverS hcoverT] using hh

run_cmd do
  for ax in (← Lean.collectAxioms ``eventually_bound) do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "EXACT DYADIC SUM OF TRIPLE FLAT ESTIMATES PASSED"

end TripleDyadicMeanSquare
