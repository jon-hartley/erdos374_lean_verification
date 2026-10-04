import FactoredDivisorHarmanRegion

/-! A uniform real cap-one factored remainder estimate at
the literal half-width X^.101/2, with a cofactor gap depending on fixed s.
This calls the general Harman mean-square theorem directly. It does not
identify actual tuple coefficients or prove a mean for an upper sector.
The saving and eventual threshold may depend on s; no uniformity as s
tends to zero is asserted. -/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set

namespace LongerTupleMeanSquare
open MellinCofactorCoverage FactoredDivisorWeights FactoredDivisorHarmanRegion

/-- For each fixed positive sieve parameter, the general factored estimate
covers products up to X^(1-s), with one factor in the stated short range.
All factor data and coefficients are uniform after fixing s. -/
theorem eventually_bound (s : ℝ) (hs : 0 < s) (hsSmall : s ≤ 1 / 1000) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
      ∀ (M N : ℕ) (sm sn : Finset ℕ) (am an : ℕ → ℝ),
        let A : ℝ := (M * N : ℕ)
        let Y : ℝ := X ^ (101 / 1000 : ℝ) / 2
        1 ≤ M → 1 ≤ N →
        X ^ (1 / 2 : ℝ) ≤ A → A ≤ X ^ (1 - s) →
        X ^ (s ^ 2 / 4) ≤ (N : ℝ) → (N : ℝ) ≤ X ^ (8 / 35 : ℝ) →
        (∀ n ∈ sm, M < n ∧ n ≤ 2 * M) →
        (∀ n ∈ sn, N < n ∧ n ≤ 2 * N) →
        (∀ n ∈ sm, |am n| ≤ 1) → (∀ n ∈ sn, |an n| ≤ 1) →
        (1 / X) * (∫ x in Icc X (2 * X),
          HarmanDivisorWindow.remainder (support sm sn) (coefficient sm sn am an)
            (x - x * (Y / X)) x ^ 2) ≤ Y ^ 2 * X ^ (-c) := by
  have hell : 0 < s / 2 := by positivity
  have hnu : 0 < s ^ 2 / 4 := by positivity
  have hrho : 0 < s / 16 := by positivity
  have hrhoEll : s / 16 ≤ s / 2 := by linarith
  have hrhoOne : s / 16 < 1 := by linarith
  have htopGap : 0 < (17991 / 20000 : ℝ) - s / 16 := by linarith
  obtain ⟨c, hc, hgeneric⟩ := FactoredDivisorMeanSquare.eventually_bound
    (1009 / 10000) (s / 2) (s ^ 2 / 4) (9 / 40000)
    (s / 16) (s / 16) (9 / 40000) 9
    (by norm_num) hell hnu (by norm_num)
    hrho hrhoEll hrhoOne hrho le_rfl (by norm_num)
  refine ⟨c, hc, ?_⟩
  filter_upwards [hgeneric,
    CofactorDoublingCoverage.eventual_scales (1 / 2) (s / 2) (s / 2)
      (by norm_num) hell hell,
    eventual_frequency_arithmetic (9 / 10000) (by norm_num) (by norm_num),
    PolynomialLogEnvelope.eventually_constant_bound 32 (s / 2)
      (by norm_num) hell,
    PolynomialLogEnvelope.eventually_constant_bound 2
      ((17991 / 20000 : ℝ) - s / 16) (by norm_num) htopGap,
    PolynomialLogEnvelope.eventually_constant_bound 2 (1 / 10000)
      (by norm_num) (by norm_num)] with X hg hcoverage hfreq hslackX htopX hwidthX
  refine ⟨hg.1, ?_⟩
  intro M N sm sn am an
  dsimp only
  intro hM hN hAlow hAupper hNlow hNupper hsm hsn ham han
  let A : ℝ := ((M * N : ℕ) : ℝ)
  let lo := lowerCutoff X A
  let H : ℝ := X ^ (s / 16)
  let U : ℝ := X ^ (17991 / 20000 : ℝ)
  let Y : ℝ := X ^ (101 / 1000 : ℝ) / 2
  have hX : 1 ≤ X := by linarith [hcoverage.1]
  have hXp : 0 < X := by linarith
  have hAp : 0 < A := by
    dsimp [A]
    exact_mod_cast Nat.mul_pos (by omega : 0 < M) (by omega : 0 < N)
  have hAX : A ≤ X := hAupper.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX (by linarith : 1 - s ≤ 1))
  have hcoverageExponent : 1 - s / 2 - s / 2 = 1 - s := by ring
  have hAcoverage : A ≤ X ^ (1 - s / 2 - s / 2) := by
    simpa only [hcoverageExponent] using hAupper
  obtain ⟨hlo, _hloone, hhi, hcap⟩ := hcoverage.2 A hAlow hAcoverage
  have hscale : 32 * A ≤ X := by
    have h32A : 32 * A ≤ X ^ (s / 2) * X ^ (1 - s) :=
      mul_le_mul hslackX.2 hAupper (by positivity) (by positivity)
    have hfull : X ^ (s / 2) * (32 * A) ≤ X := by
      calc
        _ ≤ X ^ (s / 2) * (X ^ (s / 2) * X ^ (1 - s)) :=
          mul_le_mul_of_nonneg_left h32A (by positivity)
        _ = X := by
          rw [← Real.rpow_add hXp, ← Real.rpow_add hXp]
          rw [show s / 2 + (s / 2 + (1 - s)) = 1 by ring, Real.rpow_one]
    have hpowone : 1 ≤ X ^ (s / 2) := Real.one_le_rpow hX hell.le
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
    have hpow : X ^ (s / 16) ≤ X ^ ((s / 2) / 4) :=
      Real.rpow_le_rpow_of_exponent_le hX (by linarith)
    have hroot := Real.rpow_le_rpow
      (by positivity : 0 ≤ X ^ (s / 2)) hlo
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [← Real.rpow_mul hXp.le] at hroot
    have hroot' : X ^ ((s / 2) / 4) ≤ (lo : ℝ) ^ (1 / 4 : ℝ) := by
      rw [show (s / 2) * (1 / 4 : ℝ) = (s / 2) / 4 by ring] at hroot
      exact hroot
    exact hpow.trans hroot'
  have hUlow : 2 * H ≤ U := by
    have hh := mul_le_mul_of_nonneg_right htopX.2
      (by positivity : 0 ≤ X ^ (s / 16))
    dsimp [H, U]
    calc
      _ ≤ X ^ ((17991 / 20000 : ℝ) - s / 16) * X ^ (s / 16) := hh
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
  Lean.logInfo "LONGER TUPLE ACTUAL HALF-WIDTH UNIFORM FACTORED MEAN SQUARE PASSED"

end LongerTupleMeanSquare
