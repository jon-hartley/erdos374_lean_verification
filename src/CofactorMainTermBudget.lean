import ContinuousCofactorMellin
import MellinSmoothingFunction
import MellinCofactorCoverage
import SmoothedDirichletKernel

/-!
The exact continuous cofactor main term has a smoothing multiplier.
This module bounds that multiplier and discharges the four endpoint
conditions using the common cofactor interval.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace CofactorMainTermBudget
open ContinuousCofactorMellin MellinSmoothingFunction MellinCofactorCoverage
open MellinWindowFactor Erdos374.HarmanGram152

theorem multiplier_close :
    ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ‖mellin (fun u => (Smooth1 smoothing ε u : ℂ)) 1 - 1‖ ≤
          C * ε := by
  have hbig := MellinOfSmooth1c
    MellinSmoothingFunction.differentiable MellinSmoothingFunction.support
    MellinSmoothingFunction.mass_one
  rw [Asymptotics.isBigO_iff] at hbig
  obtain ⟨c, hc⟩ := hbig
  let C := max c 1
  have hC : 0 < C := by dsimp [C]; exact lt_of_lt_of_le (by norm_num) (le_max_right c 1)
  have hset : {ε : ℝ | ‖mellin
      (fun u => (Smooth1 smoothing ε u : ℂ)) 1 - 1‖ ≤ C * ε} ∈
      𝓝[>] (0 : ℝ) := by
    filter_upwards [hc, self_mem_nhdsWithin] with ε hε hεpos
    have hp : 0 < ε := hεpos
    have hbound : ‖mellin (fun u => (Smooth1 smoothing ε u : ℂ)) 1 - 1‖ ≤
        c * ε := by simpa [Real.norm_eq_abs, abs_of_pos hp] using hε
    exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_left c 1) hp.le)
  obtain ⟨ε₀, hε₀, hsub⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset' (show (0 : ℝ) < 1 by norm_num)).mp hset
  refine ⟨C, hC, ε₀, hε₀, ?_⟩
  intro ε hε hε₀'
  exact hsub ⟨hε, hε₀'⟩

theorem covered_margins (X A x δ ε : ℝ) (d : ℕ)
    (hX : 0 < X) (hA : 0 < A)
    (hd : A < (d : ℝ) ∧ (d : ℝ) ≤ 2 * A)
    (hx : x ∈ Icc X (2 * X)) (hδ : δ ∈ Icc 0 (1 / 2))
    (hε : ε ∈ Ioo 0 (1 / 4)) :
    (d : ℝ) * lowerCutoff X A / x ≤ 1 - Real.log 2 * ε ∧
      (d : ℝ) * lowerCutoff X A / (x - x * δ) ≤
        1 - Real.log 2 * ε ∧
      1 + 2 * Real.log 2 * ε ≤
        (d : ℝ) * upperCutoff X A / x ∧
      1 + 2 * Real.log 2 * ε ≤
        (d : ℝ) * upperCutoff X A / (x - x * δ) := by
  have hxp : 0 < x := hX.trans_le hx.1
  have hleft : 0 < x - x * δ := by
    have hw := DyadicDivisorWindow.window_bounds X x δ hX hx hδ
    linarith [hw.1]
  have hleftle : x - x * δ ≤ x := by
    have hm := mul_nonneg hxp.le hδ.1
    linarith
  have hm := endpoint_margins X A x δ 1 0 d hX hA hd hx hδ
    (by constructor <;> norm_num) (by constructor <;> norm_num)
  simp only [Real.rpow_zero, mul_one] at hm
  have hlog : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlogε : Real.log 2 * ε ≤ ε :=
    by simpa using mul_le_mul_of_nonneg_right hlog hε.1.le
  have hhalf : (1 / 2 : ℝ) ≤ 1 - Real.log 2 * ε := by
    linarith [hε.2]
  have htwo : 1 + 2 * Real.log 2 * ε ≤ (2 : ℝ) := by
    nlinarith [hε.2]
  have hloX : (d : ℝ) * lowerCutoff X A / x ≤ 1 / 2 := by
    apply (div_le_iff₀ hxp).mpr
    nlinarith [hm.1]
  have hloLeft : (d : ℝ) * lowerCutoff X A / (x - x * δ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hleft).mpr
    nlinarith [hm.1]
  have hhiX : (2 : ℝ) ≤ (d : ℝ) * upperCutoff X A / x := by
    exact (le_div_iff₀ hxp).mpr hm.2
  have hhiLeft : (2 : ℝ) ≤
      (d : ℝ) * upperCutoff X A / (x - x * δ) := by
    apply (le_div_iff₀ hleft).mpr
    nlinarith [hm.2]
  exact ⟨hloX.trans hhalf, hloLeft.trans hhalf,
    htwo.trans hhiX, htwo.trans hhiLeft⟩

theorem covered_finite_main_term (X A x δ ε : ℝ)
    (s : Finset ℕ) (coeff : ℕ → ℂ)
    (hX : 0 < X) (hA : 0 < A)
    (hx : x ∈ Icc X (2 * X)) (hδ : δ ∈ Icc 0 (1 / 2))
    (hε : ε ∈ Ioo 0 (1 / 4))
    (hlo : 1 ≤ lowerCutoff X A)
    (hs : ∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 2 * A) :
    (∑ d ∈ s, coeff d *
      (∫ u in Icc (lowerCutoff X A : ℝ) (upperCutoff X A : ℝ),
        ((Smooth1 smoothing ε ((d : ℝ) * u / x) : ℝ) : ℂ) -
          ((Smooth1 smoothing ε
            ((d : ℝ) * u / (x - x * δ)) : ℝ) : ℂ))) =
      ((x * δ : ℝ) : ℂ) *
        mellin (fun y => (Smooth1 smoothing ε y : ℂ)) 1 *
        (∑ d ∈ s, coeff d / (d : ℂ)) := by
  have hxp : 0 < x := hX.trans_le hx.1
  have hleft : 0 < x - x * δ := by
    have hw := DyadicDivisorWindow.window_bounds X x δ hX hx hδ
    linarith [hw.1]
  have ha : (0 : ℝ) < lowerCutoff X A := by
    exact_mod_cast (show 0 < lowerCutoff X A by omega)
  have hab : (lowerCutoff X A : ℝ) ≤ upperCutoff X A := by
    exact_mod_cast (cutoff_strict X A hX hA).le
  have hεone : ε ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hε.1, hε.2]
  have hpos : ∀ d ∈ s, 0 < d := by
    intro d hd
    have hp := (hs d hd).1
    exact_mod_cast (hA.trans hp)
  have hm (d : ℕ) (hd : d ∈ s) :=
    covered_margins X A x δ ε d hX hA (hs d hd) hx hδ hε
  have hh := finite_continuous_main_term s coeff smoothing ε x
    (x - x * δ) (lowerCutoff X A : ℝ) (upperCutoff X A : ℝ)
    hxp hleft ha hab hpos hεone differentiable nonnegative support mass_one
    (fun d hd => (hm d hd).1)
    (fun d hd => (hm d hd).2.1)
    (fun d hd => (hm d hd).2.2.1)
    (fun d hd => (hm d hd).2.2.2)
  convert hh using 1
  · congr 1
    ring

theorem reciprocal_sum_norm_le_mass (s : Finset ℕ) (coeff : ℕ → ℂ)
    (hs : ∀ d ∈ s, 0 < d) :
    ‖∑ d ∈ s, coeff d / (d : ℂ)‖ ≤
      SmoothedDirichletKernel.coefficientMass s coeff 1 := by
  calc
    _ ≤ ∑ d ∈ s, ‖coeff d / (d : ℂ)‖ := norm_sum_le _ _
    _ = SmoothedDirichletKernel.coefficientMass s coeff 1 := by
      unfold SmoothedDirichletKernel.coefficientMass
      apply Finset.sum_congr rfl
      intro d hd
      have hdpos : (0 : ℝ) < d := by exact_mod_cast hs d hd
      rw [norm_div, Complex.norm_natCast]
      simp only [Real.rpow_neg_one]
      ring

theorem covered_main_error (X A x δ ε C : ℝ)
    (s : Finset ℕ) (coeff : ℕ → ℂ)
    (hX : 0 < X) (hA : 0 < A)
    (hx : x ∈ Icc X (2 * X)) (hδ : δ ∈ Icc 0 (1 / 2))
    (hε : ε ∈ Ioo 0 (1 / 4))
    (hlo : 1 ≤ lowerCutoff X A)
    (hs : ∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 2 * A)
    (hclose : ‖mellin (fun y => (Smooth1 smoothing ε y : ℂ)) 1 - 1‖ ≤
      C * ε) :
    ‖(∑ d ∈ s, coeff d *
        (∫ u in Icc (lowerCutoff X A : ℝ) (upperCutoff X A : ℝ),
          ((Smooth1 smoothing ε ((d : ℝ) * u / x) : ℝ) : ℂ) -
            ((Smooth1 smoothing ε
              ((d : ℝ) * u / (x - x * δ)) : ℝ) : ℂ))) -
       ((x * δ : ℝ) : ℂ) * (∑ d ∈ s, coeff d / (d : ℂ))‖ ≤
      C * ε * (x * δ) *
        SmoothedDirichletKernel.coefficientMass s coeff 1 := by
  have hxp : 0 < x := hX.trans_le hx.1
  have hw : 0 ≤ x * δ := mul_nonneg hxp.le hδ.1
  have hpos : ∀ d ∈ s, 0 < d := by
    intro d hd
    exact_mod_cast (hA.trans (hs d hd).1)
  rw [covered_finite_main_term X A x δ ε s coeff hX hA hx hδ hε hlo hs]
  have heq :
      ((x * δ : ℝ) : ℂ) *
          mellin (fun y => (Smooth1 smoothing ε y : ℂ)) 1 *
          (∑ d ∈ s, coeff d / (d : ℂ)) -
        ((x * δ : ℝ) : ℂ) * (∑ d ∈ s, coeff d / (d : ℂ)) =
      ((x * δ : ℝ) : ℂ) *
        (mellin (fun y => (Smooth1 smoothing ε y : ℂ)) 1 - 1) *
        (∑ d ∈ s, coeff d / (d : ℂ)) := by ring
  rw [heq, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hw]
  have hS := reciprocal_sum_norm_le_mass s coeff hpos
  have hCε : 0 ≤ C * ε := (norm_nonneg _).trans hclose
  calc
    _ ≤ (x * δ) * (C * ε) *
        ‖∑ d ∈ s, coeff d / (d : ℂ)‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hclose hw) (norm_nonneg _)
    _ ≤ (x * δ) * (C * ε) *
        SmoothedDirichletKernel.coefficientMass s coeff 1 :=
          mul_le_mul_of_nonneg_left hS (mul_nonneg hw hCε)
    _ = _ := by ring

theorem uniform_covered_main_error :
    ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (X A x δ ε : ℝ) (s : Finset ℕ) (coeff : ℕ → ℂ),
        0 < X → 0 < A → x ∈ Icc X (2 * X) →
        δ ∈ Icc 0 (1 / 2) → ε ∈ Ioo 0 (1 / 4) →
        ε < ε₀ → 1 ≤ lowerCutoff X A →
        (∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 2 * A) →
        ‖(∑ d ∈ s, coeff d *
            (∫ u in Icc (lowerCutoff X A : ℝ) (upperCutoff X A : ℝ),
              ((Smooth1 smoothing ε ((d : ℝ) * u / x) : ℝ) : ℂ) -
                ((Smooth1 smoothing ε
                  ((d : ℝ) * u / (x - x * δ)) : ℝ) : ℂ))) -
           ((x * δ : ℝ) : ℂ) * (∑ d ∈ s, coeff d / (d : ℂ))‖ ≤
          C * ε * (x * δ) *
            SmoothedDirichletKernel.coefficientMass s coeff 1 := by
  obtain ⟨C, hC, ε₀, hε₀, hclose⟩ := multiplier_close
  refine ⟨C, hC, ε₀, hε₀, ?_⟩
  intro X A x δ ε s coeff hX hA hx hδ hε hε₀' hlo hs
  exact covered_main_error X A x δ ε C s coeff hX hA hx hδ hε hlo hs
    (hclose ε hε.1 hε₀')

def coveredContour (X A x δ ε σ : ℝ)
    (s : Finset ℕ) (coeff : ℕ → ℂ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ, verticalDirichlet152 s coeff σ t *
      cofactor (lowerCutoff X A : ℝ) (upperCutoff X A : ℝ) (line σ t) *
      mellin (fun y => (Smooth1 smoothing ε y : ℂ)) (line σ t) *
      ((x : ℂ) ^ line σ t - ((x - x * δ : ℝ) : ℂ) ^ line σ t)

theorem covered_contour_main_error (X A x δ ε σ C : ℝ)
    (s : Finset ℕ) (coeff : ℕ → ℂ)
    (hX : 0 < X) (hA : 0 < A)
    (hx : x ∈ Icc X (2 * X)) (hδ : δ ∈ Icc 0 (1 / 2))
    (hε : ε ∈ Ioo 0 (1 / 4))
    (hσ : 1 < σ) (hσtwo : σ ≤ 2)
    (hlo : 1 ≤ lowerCutoff X A)
    (hs : ∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 2 * A)
    (hclose : ‖mellin (fun y => (Smooth1 smoothing ε y : ℂ)) 1 - 1‖ ≤
      C * ε) :
    ‖coveredContour X A x δ ε σ s coeff -
       ((x * δ : ℝ) : ℂ) * (∑ d ∈ s, coeff d / (d : ℂ))‖ ≤
      C * ε * (x * δ) *
        SmoothedDirichletKernel.coefficientMass s coeff 1 := by
  have hxp : 0 < x := hX.trans_le hx.1
  have hleft : 0 < x - x * δ := by
    have hw := DyadicDivisorWindow.window_bounds X x δ hX hx hδ
    linarith [hw.1]
  have ha : (0 : ℝ) < lowerCutoff X A := by
    exact_mod_cast (show 0 < lowerCutoff X A by omega)
  have hab : (lowerCutoff X A : ℝ) ≤ upperCutoff X A := by
    exact_mod_cast (cutoff_strict X A hX hA).le
  have hεone : ε ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hε.1, hε.2]
  have hpos : ∀ d ∈ s, 0 < d := by
    intro d hd
    exact_mod_cast (hA.trans (hs d hd).1)
  have hmain := covered_main_error X A x δ ε C s coeff hX hA hx hδ
    hε hlo hs hclose
  rw [finite_short_window_integrand s coeff smoothing ε σ x (x - x * δ)
    (lowerCutoff X A : ℝ) (upperCutoff X A : ℝ) hxp hleft ha hab hpos
    hσ hσtwo hεone differentiable nonnegative support mass_one] at hmain
  exact hmain

theorem uniform_covered_contour_main_error :
    ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (X A x δ ε σ : ℝ) (s : Finset ℕ) (coeff : ℕ → ℂ),
        0 < X → 0 < A → x ∈ Icc X (2 * X) →
        δ ∈ Icc 0 (1 / 2) → ε ∈ Ioo 0 (1 / 4) → ε < ε₀ →
        1 < σ → σ ≤ 2 → 1 ≤ lowerCutoff X A →
        (∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 2 * A) →
        ‖coveredContour X A x δ ε σ s coeff -
          ((x * δ : ℝ) : ℂ) * (∑ d ∈ s, coeff d / (d : ℂ))‖ ≤
          C * ε * (x * δ) *
            SmoothedDirichletKernel.coefficientMass s coeff 1 := by
  obtain ⟨C, hC, ε₀, hε₀, hclose⟩ := multiplier_close
  refine ⟨C, hC, ε₀, hε₀, ?_⟩
  intro X A x δ ε σ s coeff hX hA hx hδ hε hε₀' hσ hσtwo hlo hs
  exact covered_contour_main_error X A x δ ε σ C s coeff hX hA hx hδ
    hε hσ hσtwo hlo hs (hclose ε hε.1 hε₀')

end CofactorMainTermBudget

run_cmd do
  for target in [``CofactorMainTermBudget.multiplier_close,
      ``CofactorMainTermBudget.covered_margins,
      ``CofactorMainTermBudget.covered_finite_main_term,
      ``CofactorMainTermBudget.reciprocal_sum_norm_le_mass,
      ``CofactorMainTermBudget.covered_main_error,
      ``CofactorMainTermBudget.uniform_covered_main_error,
      ``CofactorMainTermBudget.covered_contour_main_error,
      ``CofactorMainTermBudget.uniform_covered_contour_main_error] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "COFACTOR MAIN TERM BUDGET PASSED"
