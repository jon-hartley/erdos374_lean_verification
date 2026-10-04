import FiniteWindowFrequencySplit

/-!
Extend the finite short-window approximation to signed real weights.
Positive and negative parts use the same support, smoothing, contour,
and cutoff. Their two errors are added explicitly.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace SignedFiniteWindowApproximation
open SmoothedCountBoundary SmoothedWindowTransfer
open Erdos374.HarmanGram152

def positivePart (weight : ℕ → ℝ) (n : ℕ) : ℝ := max (weight n) 0
def negativePart (weight : ℕ → ℝ) (n : ℕ) : ℝ := max (-weight n) 0

theorem decomposition (weight : ℕ → ℝ) :
    weight = fun n => positivePart weight n - negativePart weight n := by
  funext n
  unfold positivePart negativePart
  by_cases h : 0 ≤ weight n
  · rw [max_eq_left h, max_eq_right (by linarith : -weight n ≤ 0)]
    ring
  · rw [max_eq_right (by linarith : weight n ≤ 0), max_eq_left (by linarith : 0 ≤ -weight n)]
    ring

theorem sharp_sub (s : Finset ℕ) (left right : ℕ → ℝ) (x : ℝ) :
    sharp s (fun n => left n - right n) x = sharp s left x - sharp s right x := by
  unfold sharp
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> ring

theorem vertical_sub (s : Finset ℕ) (left right : ℕ → ℝ) (σ t : ℝ) :
    verticalDirichlet152 s (fun n => ((left n - right n : ℝ) : ℂ)) σ t =
      verticalDirichlet152 s (fun n => (left n : ℂ)) σ t -
        verticalDirichlet152 s (fun n => (right n : ℂ)) σ t := by
  simp only [verticalDirichlet152, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib]

theorem transform_sub (s : Finset ℕ) (left right : ℕ → ℝ) (ε a b σ δ x : ℝ)
    (hx : 0 < x) (hleft : 0 < x - x * δ) (hs : ∀ n ∈ s, 0 < n)
    (hσ : 1 < σ) (hσtwo : σ ≤ 2) (hε : ε ∈ Ioo 0 1) :
    transform (verticalDirichlet152 s (fun n => ((left n - right n : ℝ) : ℂ)) σ)
      MellinSmoothingFunction.smoothing ε a b σ δ x =
    transform (verticalDirichlet152 s (fun n => (left n : ℂ)) σ)
      MellinSmoothingFunction.smoothing ε a b σ δ x -
    transform (verticalDirichlet152 s (fun n => (right n : ℂ)) σ)
      MellinSmoothingFunction.smoothing ε a b σ δ x := by
  unfold transform
  simp_rw [vertical_sub, sub_mul]
  exact integral_sub
    (FiniteWindowFrequencySplit.integrable_kernel s left ε σ δ x hx hleft hs hσ hσtwo hε).integrableOn
    (FiniteWindowFrequencySplit.integrable_kernel s right ε σ δ x hx hleft hs hσ hσtwo hε).integrableOn

def error (s : Finset ℕ) (weight : ℕ → ℝ) (ε a b σ δ x : ℝ) : ℂ :=
  ((sharp s weight x - sharp s weight (x - x * δ) : ℝ) : ℂ) -
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      transform (verticalDirichlet152 s (fun n => (weight n : ℂ)) σ)
        MellinSmoothingFunction.smoothing ε a b σ δ x

theorem error_sub (s : Finset ℕ) (left right : ℕ → ℝ) (ε a b σ δ x : ℝ)
    (hx : 0 < x) (hleft : 0 < x - x * δ) (hs : ∀ n ∈ s, 0 < n)
    (hσ : 1 < σ) (hσtwo : σ ≤ 2) (hε : ε ∈ Ioo 0 1) :
    error s (fun n => left n - right n) ε a b σ δ x =
      error s left ε a b σ δ x - error s right ε a b σ δ x := by
  unfold error
  rw [sharp_sub, sharp_sub, transform_sub s left right ε a b σ δ x hx hleft hs hσ hσtwo hε]
  push_cast
  ring

theorem eventual_approximation : ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
    ∀ (s : Finset ℕ) (weight : ℕ → ℝ) (B : ℕ) (x δ : ℝ),
      1 ≤ B → (B : ℝ) ≤ X ^ (2 : ℕ) →
      (∀ n ∈ s, 0 < n ∧ n ≤ B) →
      (∀ n ∈ s, |weight n| ≤ X ^ (1 / 200 : ℝ)) →
      x ∈ Icc X (2 * X) → δ ∈ Icc 0 (1 / 2) →
      ‖error s weight (X ^ (-19 / 20 : ℝ)) (-X) X
        (1 + 1 / Real.log X) δ x‖ ≤ 4 * X ^ (2 / 25 : ℝ) := by
  filter_upwards [FiniteWindowApproximation.eventual_approximation] with X hX
  refine ⟨hX.1, ?_⟩
  intro s weight B x δ hB hBX hs hw hx hδ
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hX.1
  have hxp : 0 < x := hXp.trans_le hx.1
  have hleft : 0 < x - x * δ := by
    have hh := mul_le_mul_of_nonneg_left hδ.2 hxp.le
    linarith
  have hlog : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX.1
  have hσ : 1 < 1 + 1 / Real.log X := by
    have hh : 0 < 1 / Real.log X := by positivity
    linarith
  have hσtwo : 1 + 1 / Real.log X ≤ 2 := by
    have hh : 1 / Real.log X ≤ 1 := (div_le_one (by linarith)).mpr hlog
    linarith
  have hε : X ^ (-19 / 20 : ℝ) ∈ Ioo 0 1 :=
    ⟨Real.rpow_pos_of_pos hXp _, Real.rpow_lt_one_of_one_lt_of_neg
      ((Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hX.1) (by norm_num)⟩
  have hpositive : ∀ n ∈ s, 0 ≤ positivePart weight n ∧
      positivePart weight n ≤ X ^ (1 / 200 : ℝ) := by
    intro n hn
    exact ⟨le_max_right _ _, max_le ((le_abs_self _).trans (hw n hn)) (by positivity)⟩
  have hnegative : ∀ n ∈ s, 0 ≤ negativePart weight n ∧
      negativePart weight n ≤ X ^ (1 / 200 : ℝ) := by
    intro n hn
    exact ⟨le_max_right _ _, max_le ((neg_le_abs _).trans (hw n hn)) (by positivity)⟩
  have hp := hX.2 s (positivePart weight) B x δ hB hBX hs hpositive hx hδ
  have hn := hX.2 s (negativePart weight) B x δ hB hBX hs hnegative hx hδ
  have hid : error s weight (X ^ (-19 / 20 : ℝ)) (-X) X
      (1 + 1 / Real.log X) δ x =
      error s (positivePart weight) (X ^ (-19 / 20 : ℝ)) (-X) X
        (1 + 1 / Real.log X) δ x -
      error s (negativePart weight) (X ^ (-19 / 20 : ℝ)) (-X) X
        (1 + 1 / Real.log X) δ x := by
    calc
      _ = error s (fun n => positivePart weight n - negativePart weight n)
          (X ^ (-19 / 20 : ℝ)) (-X) X (1 + 1 / Real.log X) δ x :=
        congrArg (fun w => error s w (X ^ (-19 / 20 : ℝ)) (-X) X
          (1 + 1 / Real.log X) δ x) (decomposition weight)
      _ = _ := error_sub s (positivePart weight) (negativePart weight) _ _ _ _ _ _
        hxp hleft (fun n hn => (hs n hn).1) hσ hσtwo hε
  rw [hid]
  exact (norm_sub_le _ _).trans (by dsimp only [error]; linarith)

end SignedFiniteWindowApproximation

#print axioms SignedFiniteWindowApproximation.eventual_approximation
run_cmd do
  for target in [``SignedFiniteWindowApproximation.sharp_sub,
      ``SignedFiniteWindowApproximation.transform_sub,
      ``SignedFiniteWindowApproximation.eventual_approximation] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "SIGNED FINITE WINDOW APPROXIMATION PASSED"
