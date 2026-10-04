import FactoredDivisorVariableWindow
import FactoredDivisorScaling
import FiniteDivisorFamily

/-!
Uniform finite-family mean square for the actual variable window. The positive
saving and threshold precede Y, all block data, and all factor weights.
Overlapping supports and signs are retained by the exact family coefficient.
-/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
namespace FactoredDivisorVariableWindow
open FactoredDivisorHarmanRegion

theorem eventually_bound {ι : Type*} (α ell slack nu ε : ℝ)
    (hα : 0 < α) (hell : 0 < ell)
    (hslack : 0 < slack) (hnu : 0 < nu)
    (hε : 0 < ε) (hεsmall : ε < 1 / 100) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
        ∀ (Y : ℝ) (family : Finset ι) (M N : ι → ℕ)
          (sm sn : ι → Finset ℕ) (am an : ι → ℕ → ℝ),
          let supports := fun i => FactoredDivisorWeights.support (sm i) (sn i)
          let weights := fun i =>
            FactoredDivisorWeights.coefficient (sm i) (sn i) (am i) (an i)
          X ^ windowExponent ε ≤ Y → Y ≤ X / 2 →
          (family.card : ℝ) ≤ X ^ (c / 2) →
          (∀ i ∈ family,
            1 ≤ M i ∧ 1 ≤ N i ∧
            X ^ α ≤ ((M i * N i : ℕ) : ℝ) ∧
            ((M i * N i : ℕ) : ℝ) ≤ X ^ (1 - ell - slack) ∧
            X ^ nu ≤ (N i : ℝ) ∧
            ((N i : ℝ) ≤ X ^ (8 / 35 : ℝ) ∨
              X ^ (27 / 35 : ℝ) ≤ ((M i * N i : ℕ) : ℝ)) ∧
            (∀ n ∈ sm i, M i < n ∧ n ≤ 2 * M i) ∧
            (∀ n ∈ sn i, N i < n ∧ n ≤ 2 * N i) ∧
            (∀ n ∈ sm i, |am i n| ≤ X ^ (c / 2)) ∧
            (∀ n ∈ sn i, |an i n| ≤ X ^ (c / 2))) →
          (1 / X) * (∫ x in Icc X (2 * X),
            HarmanDivisorWindow.remainder
              (FiniteDivisorFamily.support family supports)
              (FiniteDivisorFamily.coefficient family supports weights)
              (x - x * (Y / X)) x ^ 2) ≤ Y ^ 2 * X ^ (-c) := by
  obtain ⟨γ, hγ, hgeneric⟩ :=
    FactoredDivisorVariableWindow.eventually_region α ell slack nu ε
      hα hell hslack hnu hε hεsmall
  refine ⟨γ / 4, by positivity, ?_⟩
  filter_upwards [hgeneric] with X hh
  refine ⟨hh.1, ?_⟩
  intro Y family M N sm sn am an
  dsimp only
  intro hYlower hYhalf hcard hdata
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hh.1
  have hXone : 1 ≤ X :=
    (by norm_num : (1 : ℝ) ≤ Real.exp 1).trans hh.1
  have hY : 0 ≤ Y := (Real.rpow_pos_of_pos hXp _).le.trans hYlower
  have hYX : Y ≤ X := by linarith
  have hB : 0 < X ^ (γ / 8) := Real.rpow_pos_of_pos hXp _
  have hquarter : (γ / 4) / 2 = γ / 8 := by ring
  have hfamilyQuarter : (γ / 2) / 4 = γ / 8 := by ring
  have hcard' : (family.card : ℝ) ≤ X ^ ((γ / 2) / 4) := by
    simpa only [hquarter, hfamilyQuarter] using hcard
  have hmean : ∀ i ∈ family,
      (1 / X) * (∫ x in Icc X (2 * X),
        HarmanDivisorWindow.remainder
          (FactoredDivisorWeights.support (sm i) (sn i))
          (FactoredDivisorWeights.coefficient (sm i) (sn i) (am i) (an i))
          (x - x * (Y / X)) x ^ 2) ≤
            (Y) ^ 2 * X ^ (-(γ / 2)) := by
    intro i hi
    rcases hdata i hi with
      ⟨hM, hN, hAlow, hAupper, hNlow, hbranch, hsm, hsn, ham, han⟩
    have hm : ∀ n ∈ sm i, |am i n / X ^ (γ / 8)| ≤ 1 := by
      intro n hn
      rw [abs_div, abs_of_pos hB]
      apply (div_le_one hB).mpr
      simpa only [hquarter] using ham n hn
    have hn : ∀ n ∈ sn i, |an i n / X ^ (γ / 8)| ≤ 1 := by
      intro n hn
      rw [abs_div, abs_of_pos hB]
      apply (div_le_one hB).mpr
      simpa only [hquarter] using han n hn
    have hnormalized := hh.2 Y (M i) (N i) (sm i) (sn i)
      (fun n => am i n / X ^ (γ / 8))
      (fun n => an i n / X ^ (γ / 8))
      hYlower hYhalf hM hN hAlow hAupper hNlow hbranch hsm hsn hm hn
    rw [FactoredDivisorScaling.normalized_mean_square
      (sm i) (sn i) (am i) (an i)
      (X ^ (γ / 8)) X (Y / X) hB.ne']
    apply (mul_le_mul_of_nonneg_left hnormalized (by positivity :
      0 ≤ (X ^ (γ / 8)) ^ (4 : ℕ))).trans
    have heq : (X ^ (γ / 8)) ^ (4 : ℕ) *
        ((Y) ^ 2 * X ^ (-γ)) =
          (Y) ^ 2 * X ^ (-(γ / 2)) := by
      rw [← Real.rpow_mul_natCast hXp.le]
      calc
        _ = (Y) ^ 2 *
            (X ^ ((γ / 8) * (4 : ℕ)) * X ^ (-γ)) := by ring
        _ = (Y) ^ 2 *
            X ^ ((γ / 8) * (4 : ℕ) + -γ) := by
              rw [← Real.rpow_add hXp]
        _ = _ := by congr 1; ring
    exact heq.le
  have hcombined := FiniteDivisorFamily.normalized_power_bound
    family (fun i => FactoredDivisorWeights.support (sm i) (sn i))
    (fun i => FactoredDivisorWeights.coefficient (sm i) (sn i) (am i) (an i))
    X (Y) (γ / 2) hXp hY hYX hcard' hmean
  simpa only [show (γ / 2) / 2 = γ / 4 by ring] using hcombined

end FactoredDivisorVariableWindow

#print axioms FactoredDivisorVariableWindow.eventually_bound
run_cmd do
  let axioms ← Lean.collectAxioms ``FactoredDivisorVariableWindow.eventually_bound
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "FACTORED DIVISOR VARIABLE WINDOW FAMILY PASSED"
