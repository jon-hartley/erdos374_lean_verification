import FactoredDivisorHarmanRegion

/-! A uniform real cap-one factored remainder estimate at the actual
half-width X^.101/2. The floor counting cofactor and its nine-block
coverage are inherited from the general Harman mean-square theorem.
This module does not identify an actual sieve singleton coefficient. -/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set

namespace ShortSingletonMeanSquare
open MellinCofactorCoverage FactoredDivisorWeights FactoredDivisorHarmanRegion

/-- The exact short-factor range, with the half-width kept literal and
with the saving and eventual threshold uniform over all factor data. -/
theorem eventually_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
      ∀ (M N : ℕ) (sm sn : Finset ℕ) (am an : ℕ → ℝ),
        let A : ℝ := (M * N : ℕ)
        let Y : ℝ := X ^ (101 / 1000 : ℝ) / 2
        1 ≤ M → 1 ≤ N →
        X ^ (59 / 200 : ℝ) ≤ A → A ≤ X ^ (731 / 1000 : ℝ) →
        X ^ (39 / 1000 : ℝ) ≤ (N : ℝ) → (N : ℝ) ≤ X ^ (8 / 35 : ℝ) →
        (∀ n ∈ sm, M < n ∧ n ≤ 2 * M) →
        (∀ n ∈ sn, N < n ∧ n ≤ 2 * N) →
        (∀ n ∈ sm, |am n| ≤ 1) → (∀ n ∈ sn, |an n| ≤ 1) →
        (1 / X) * (∫ x in Icc X (2 * X),
          HarmanDivisorWindow.remainder (support sm sn) (coefficient sm sn am an)
            (x - x * (Y / X)) x ^ 2) ≤ Y ^ 2 * X ^ (-c) := by
  obtain ⟨c, hc, hgeneric⟩ := FactoredDivisorMeanSquare.eventually_bound
    (1009 / 10000) (67 / 250) (39 / 1000) (9 / 40000)
    (67 / 2000) (67 / 2000) (9 / 40000) 9
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨c, hc, ?_⟩
  filter_upwards [hgeneric,
    CofactorDoublingCoverage.eventual_scales (59 / 200) (67 / 250) (1 / 1000)
      (by norm_num) (by norm_num) (by norm_num),
    eventual_frequency_arithmetic (9 / 10000) (by norm_num) (by norm_num),
    PolynomialLogEnvelope.eventually_constant_bound 32 (1 / 1000)
      (by norm_num) (by norm_num),
    PolynomialLogEnvelope.eventually_constant_bound 2
      ((17991 / 20000 : ℝ) - 67 / 2000) (by norm_num) (by norm_num),
    PolynomialLogEnvelope.eventually_constant_bound 2 (1 / 10000)
      (by norm_num) (by norm_num)] with X hg hcoverage hfreq hslackX htopX hwidthX
  refine ⟨hg.1, ?_⟩
  intro M N sm sn am an
  dsimp only
  intro hM hN hAlow hAupper hNlow hNupper hsm hsn ham han
  let A : ℝ := ((M * N : ℕ) : ℝ)
  let lo := lowerCutoff X A
  let H : ℝ := X ^ (67 / 2000 : ℝ)
  let U : ℝ := X ^ (17991 / 20000 : ℝ)
  let Y : ℝ := X ^ (101 / 1000 : ℝ) / 2
  have hX : 1 ≤ X := by linarith [hcoverage.1]
  have hXp : 0 < X := by linarith
  have hAp : 0 < A := by
    dsimp [A]
    exact_mod_cast Nat.mul_pos (by omega : 0 < M) (by omega : 0 < N)
  have hAX : A ≤ X := hAupper.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (731 / 1000 : ℝ) ≤ 1))
  have hAcoverage : A ≤ X ^ (1 - (67 / 250 : ℝ) - 1 / 1000) := by
    convert hAupper using 1
    norm_num
  obtain ⟨hlo, _hloone, hhi, hcap⟩ := hcoverage.2 A hAlow hAcoverage
  have hscale : 32 * A ≤ X := by
    have h32A : 32 * A ≤ X ^ (1 / 1000 : ℝ) * X ^ (731 / 1000 : ℝ) :=
      mul_le_mul hslackX.2 hAupper (by positivity) (by positivity)
    have hfull : X ^ (67 / 250 : ℝ) * (32 * A) ≤ X := by
      calc
        _ ≤ X ^ (67 / 250 : ℝ) *
            (X ^ (1 / 1000 : ℝ) * X ^ (731 / 1000 : ℝ)) :=
          mul_le_mul_of_nonneg_left h32A (by positivity)
        _ = X := by
          rw [← Real.rpow_add hXp, ← Real.rpow_add hXp]
          norm_num
    have hpowone : 1 ≤ X ^ (67 / 250 : ℝ) :=
      Real.one_le_rpow hX (by norm_num)
    nlinarith [hfull]
  have hloScale : X / (32 * A) ≤ (lo : ℝ) :=
    lowerCutoff_scale X A hAp hscale
  obtain ⟨hproduct, hpair⟩ := pair_total_guards X A (9 / 10000) lo M N
    hX rfl hM hN hloScale (by norm_num) hfreq.2.1 (Or.inl hNupper)
  have hselection : selectionExponent (9 / 10000) = (9 / 40000 : ℝ) := by
    norm_num [selectionExponent]
  have htail : tailExponent (9 / 10000) = (17991 / 20000 : ℝ) := by
    norm_num [tailExponent]
  rw [hselection, htail] at hproduct hpair
  have hHroot : H ≤ (lo : ℝ) ^ (1 / 4 : ℝ) := by
    have hpow : X ^ (67 / 2000 : ℝ) ≤ X ^ ((67 / 250 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
    have hroot := Real.rpow_le_rpow
      (by positivity : 0 ≤ X ^ (67 / 250 : ℝ)) hlo
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [← Real.rpow_mul hXp.le] at hroot
    have hroot' : X ^ ((67 / 250 : ℝ) / 4) ≤ (lo : ℝ) ^ (1 / 4 : ℝ) := by
      convert hroot using 1
      norm_num
    exact hpow.trans hroot'
  have hUlow : 2 * H ≤ U := by
    have hh := mul_le_mul_of_nonneg_right htopX.2
      (by positivity : 0 ≤ X ^ (67 / 2000 : ℝ))
    dsimp [H, U]
    calc
      _ ≤ X ^ ((17991 / 20000 : ℝ) - 67 / 2000) * X ^ (67 / 2000 : ℝ) := hh
      _ = X ^ (17991 / 20000 : ℝ) := by
        rw [← Real.rpow_add hXp]
        congr 1
        ring
  have hUX : U ≤ X := by
    dsimp [U]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (17991 / 20000 : ℝ) ≤ 1)
  have hUhigh : X ^ (1 - (1009 / 10000 : ℝ) + 9 / 40000) ≤ U := by
    exact Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
  have hYlow : X ^ (1009 / 10000 : ℝ) ≤ Y := by
    dsimp [Y]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    calc
      _ ≤ X ^ (1009 / 10000 : ℝ) * X ^ (1 / 10000 : ℝ) :=
        mul_le_mul_of_nonneg_left hwidthX.2 (by positivity)
      _ = X ^ (101 / 1000 : ℝ) := by
        rw [← Real.rpow_add hXp]
        norm_num
  have hYhalf : Y ≤ X / 2 := by
    dsimp [Y]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (101 / 1000 : ℝ) ≤ 1)
  have hcall := hg.2 M N sm sn am an Y H U
  dsimp only at hcall
  apply hcall hM hN hAX hlo hhi hcap hNlow hproduct hpair
  · exact le_rfl
  · exact hHroot
  · nlinarith [hUlow, (show 0 ≤ H by positivity)]
  · exact hUlow
  · exact hUX
  · exact hUhigh
  · exact hYlow
  · exact hYhalf
  · exact hsm
  · exact hsn
  · exact ham
  · exact han

#print axioms eventually_bound
run_cmd do
  for ax in (← Lean.collectAxioms ``eventually_bound) do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "SHORT SINGLETON ACTUAL HALF-WIDTH UNIFORM FACTORED MEAN SQUARE PASSED"

end ShortSingletonMeanSquare
