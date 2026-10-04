import FactoredDivisorHarmanRegion

/-!
Uniform variable-window extension of the factored-divisor Harman region.
The same fixed frequency choices are checked against the generic mean-square
estimate for every X^(1/10+ε) ≤ Y ≤ X/2. No comparison of signed remainders
at different window widths is used. The imported package is kept immutable.
-/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
namespace FactoredDivisorVariableWindow
open MellinCofactorCoverage FactoredDivisorWeights FactoredDivisorHarmanRegion

theorem eventually_region (α ell slack nu ε : ℝ)
    (hα : 0 < α) (hell : 0 < ell)
    (hslack : 0 < slack) (hnu : 0 < nu)
    (hε : 0 < ε) (hεsmall : ε < 1 / 100) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
        ∀ (Y : ℝ) (M N : ℕ) (sm sn : Finset ℕ) (am an : ℕ → ℝ),
          let A : ℝ := (M * N : ℕ)
          X ^ windowExponent ε ≤ Y → Y ≤ X / 2 →
          1 ≤ M → 1 ≤ N →
          X ^ α ≤ A → A ≤ X ^ (1 - ell - slack) →
          X ^ nu ≤ (N : ℝ) →
          ((N : ℝ) ≤ X ^ (8 / 35 : ℝ) ∨
            X ^ (27 / 35 : ℝ) ≤ A) →
          (∀ n ∈ sm, M < n ∧ n ≤ 2 * M) →
          (∀ n ∈ sn, N < n ∧ n ≤ 2 * N) →
          (∀ n ∈ sm, |am n| ≤ 1) →
          (∀ n ∈ sn, |an n| ≤ 1) →
          (1 / X) * (∫ x in Icc X (2 * X),
            HarmanDivisorWindow.remainder
              (FactoredDivisorWeights.support sm sn)
              (FactoredDivisorWeights.coefficient sm sn am an)
              (x - x * (Y / X)) x ^ 2) ≤ Y ^ 2 * X ^ (-c) := by
  obtain ⟨hηpos, hηell, hηone, hηfour, hηtop⟩ :=
    eta_properties ell ε hell hεsmall
  obtain ⟨c, hc, hgeneric⟩ :=
    FactoredDivisorMeanSquare.eventually_bound
      (windowExponent ε) ell nu (selectionExponent ε)
      (eta ell) (eta ell) (capExponent ε) 9
      (by dsimp [windowExponent]; linarith) hell hnu
      (by dsimp [selectionExponent]; positivity)
      hηpos hηell hηone hηpos le_rfl
      (by dsimp [capExponent]; positivity)
  refine ⟨c, hc, ?_⟩
  filter_upwards [hgeneric,
    CofactorDoublingCoverage.eventual_scales α ell slack hα hell hslack,
    eventual_frequency_arithmetic ε hε hεsmall,
    PolynomialLogEnvelope.eventually_constant_bound
      32 slack (by norm_num) hslack,
    PolynomialLogEnvelope.eventually_constant_bound
      2 (tailExponent ε - eta ell) (by norm_num) (by linarith),
    eventually_ge_atTop (Real.exp 1)] with X hg hcoverage hfreq
      hslackX htopX hXexp
  refine ⟨hXexp, ?_⟩
  intro Y M N sm sn am an
  dsimp only
  intro hYlower hYhalf hM hN hAlow hAupper hNlow hbranch hsm hsn ham han
  let A : ℝ := ((M * N : ℕ) : ℝ)
  let lo := lowerCutoff X A
  let hi := upperCutoff X A
  let H : ℝ := X ^ eta ell
  let U : ℝ := X ^ tailExponent ε
  have hX : 1 ≤ X := hfreq.1
  have hXp : 0 < X := by linarith
  have hAp : 0 < A := by
    dsimp [A]
    exact_mod_cast Nat.mul_pos (by omega : 0 < M) (by omega : 0 < N)
  have hAone : 1 ≤ A := by
    dsimp [A]
    exact_mod_cast Nat.mul_le_mul hM hN
  have hAX : A ≤ X := by
    have hexp : 1 - ell - slack ≤ (1 : ℝ) := by linarith
    exact hAupper.trans (by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hX hexp)
  obtain ⟨hlo, _hloone, hhi, hcap⟩ :=
    hcoverage.2 A hAlow hAupper
  have hscale : 32 * A ≤ X := by
    have h32A : 32 * A ≤
        X ^ slack * X ^ (1 - ell - slack) := by
      exact mul_le_mul hslackX.2 hAupper
        (by positivity : 0 ≤ A)
        (Real.rpow_nonneg hXp.le _)
    have hfull : X ^ ell * (32 * A) ≤ X := by
      calc
        _ ≤ X ^ ell * (X ^ slack * X ^ (1 - ell - slack)) :=
          mul_le_mul_of_nonneg_left h32A (by positivity)
        _ = X := by
          rw [← Real.rpow_add hXp, ← Real.rpow_add hXp]
          convert Real.rpow_one X using 1
          ring
    have hpowone : 1 ≤ X ^ ell := Real.one_le_rpow hX hell.le
    nlinarith [hfull]
  have hloScale : X / (32 * A) ≤ (lo : ℝ) :=
    lowerCutoff_scale X A hAp hscale
  obtain ⟨hproduct, hpair⟩ := pair_total_guards X A ε lo M N
    hX rfl hM hN hloScale hε hfreq.2.1 hbranch
  have hHroot : H ≤ (lo : ℝ) ^ (1 / 4 : ℝ) := by
    have hpow : X ^ (eta ell) ≤ X ^ (ell / 4) :=
      Real.rpow_le_rpow_of_exponent_le hX hηfour
    have hroot := Real.rpow_le_rpow
      (by positivity : 0 ≤ X ^ ell) hlo
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [← Real.rpow_mul hXp.le] at hroot
    have hroot' : X ^ (ell / 4) ≤
        (lo : ℝ) ^ (1 / 4 : ℝ) := by
      convert hroot using 1
      ring
    exact hpow.trans hroot'
  have hUlow : 2 * H ≤ U := by
    have hh := mul_le_mul_of_nonneg_right htopX.2
      (by positivity : 0 ≤ X ^ eta ell)
    dsimp [H, U]
    calc
      _ ≤ X ^ (tailExponent ε - eta ell) * X ^ eta ell := hh
      _ = X ^ tailExponent ε := by
        rw [← Real.rpow_add hXp]
        congr 1
        ring
  have hUX : U ≤ X := by
    dsimp [U]
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hX
      (by dsimp [tailExponent]; linarith : tailExponent ε ≤ 1))
  have hUhigh : X ^ (1 - windowExponent ε + capExponent ε) ≤ U := by
    dsimp [U]
    exact Real.rpow_le_rpow_of_exponent_le hX
      (by dsimp [windowExponent, capExponent, tailExponent]; linarith)
  have hcall := hg.2 M N sm sn am an Y H U
  dsimp only at hcall
  apply hcall hM hN hAX hlo hhi hcap hNlow hproduct hpair
  · exact le_rfl
  · exact hHroot
  · nlinarith [hUlow, (show 0 ≤ H by positivity)]
  · exact hUlow
  · exact hUX
  · exact hUhigh
  · exact hYlower
  · exact hYhalf
  · exact hsm
  · exact hsn
  · exact ham
  · exact han

end FactoredDivisorVariableWindow

#print axioms FactoredDivisorVariableWindow.eventually_region
run_cmd do
  let axioms ← Lean.collectAxioms ``FactoredDivisorVariableWindow.eventually_region
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "FACTORED DIVISOR VARIABLE WINDOW REGION PASSED"
