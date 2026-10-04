import HarmanDivisorContour
import PolynomialLogEnvelope

/-!
Common cofactor cutoffs for actual signed divisor windows. The divisor
scale A is real. The finite product support is at most 4X, regardless
of its convolution multiplicities. The contour approximation uses the
existing signed divisor theorem and retains its explicit weight bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter Set
open scoped BigOperators

namespace DyadicDivisorWindow
open HarmanDivisorWindow

def divisorCutoff (A : ℝ) : ℕ := ⌊2 * A⌋₊
def lowerCutoff (X A : ℝ) : ℕ := ⌊X / (4 * A)⌋₊
def upperCutoff (X A : ℝ) : ℕ := ⌊2 * X / A⌋₊
def cofactors (X A : ℝ) : Finset ℕ :=
  Finset.Ioc (lowerCutoff X A) (upperCutoff X A)

theorem window_bounds (X x δ : ℝ) (hX : 0 < X)
    (hx : x ∈ Icc X (2 * X)) (hδ : δ ∈ Icc 0 (1 / 2)) :
    X / 2 ≤ x - x * δ ∧ x - x * δ ≤ x := by
  have hxp : 0 ≤ x := hX.le.trans hx.1
  have hhigh := mul_le_mul_of_nonneg_left hδ.2 hxp
  have hlow := mul_nonneg hxp hδ.1
  constructor <;> linarith [hx.1]

theorem floor_coverage (X A x δ : ℝ) (d : ℕ)
    (hX : 0 < X) (hA : 0 < A) (hd : A < (d : ℝ) ∧ (d : ℝ) ≤ 2 * A)
    (hx : x ∈ Icc X (2 * X)) (hδ : δ ∈ Icc 0 (1 / 2)) :
    lowerCutoff X A ≤ ⌊(x - x * δ) / d⌋₊ ∧
      ⌊x / d⌋₊ ≤ upperCutoff X A := by
  have hdp : (0 : ℝ) < d := hA.trans hd.1
  have hw := window_bounds X x δ hX hx hδ
  have hleft : 0 ≤ x - x * δ := by linarith
  constructor
  · apply Nat.floor_mono
    calc
      X / (4 * A) = (X / 2) / (2 * A) := by ring
      _ ≤ (x - x * δ) / (2 * A) :=
        div_le_div_of_nonneg_right hw.1 (by positivity)
      _ ≤ (x - x * δ) / d :=
        div_le_div_of_nonneg_left hleft hdp hd.2
  · apply Nat.floor_mono
    calc
      x / d ≤ (2 * X) / d := div_le_div_of_nonneg_right hx.2 hdp.le
      _ ≤ (2 * X) / A :=
        div_le_div_of_nonneg_left (by positivity) hA hd.1.le

theorem divisor_bounds (A : ℝ) (d : ℕ) (hA : 0 < A)
    (hd : A < (d : ℝ) ∧ (d : ℝ) ≤ 2 * A) :
    0 < d ∧ d ≤ divisorCutoff A := by
  constructor
  · exact_mod_cast hA.trans hd.1
  · exact (Nat.le_floor_iff (by positivity : 0 ≤ 2 * A)).mpr hd.2

theorem cutoff_order (X A : ℝ) (hX : 0 ≤ X) (hA : 0 < A) :
    lowerCutoff X A ≤ upperCutoff X A := by
  apply Nat.floor_mono
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * A) hA).mpr
  nlinarith

theorem lowerCutoff_positive (X A : ℝ) (hA : 0 < A) (hscale : 4 * A ≤ X) :
    1 ≤ lowerCutoff X A := by
  have hX : 0 ≤ X := by linarith
  apply (Nat.le_floor_iff (by positivity : 0 ≤ X / (4 * A))).mpr
  norm_num only [Nat.cast_one]
  exact (one_le_div₀ (by positivity : 0 < 4 * A)).mpr hscale

theorem lowerCutoff_scale (X A : ℝ) (hA : 0 < A) (hscale : 8 * A ≤ X) :
    X / (8 * A) ≤ (lowerCutoff X A : ℝ) := by
  have hq : (2 : ℝ) ≤ X / (4 * A) :=
    (le_div_iff₀ (by positivity : 0 < 4 * A)).mpr (by nlinarith)
  have hf := Nat.lt_floor_add_one (X / (4 * A))
  have heq : X / (8 * A) = (X / (4 * A)) / 2 := by ring
  rw [heq]
  change (X / (4 * A)) / 2 ≤ (⌊X / (4 * A)⌋₊ : ℝ)
  linarith

theorem cofactor_bounds (X A : ℝ) (hX : 0 ≤ X) (hA : 0 < A)
    (k : ℕ) (hk : k ∈ cofactors X A) :
    0 < k ∧ X / (4 * A) < (k : ℝ) ∧ (k : ℝ) ≤ 2 * X / A := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hk
  refine ⟨by omega, ?_, ?_⟩
  · exact (Nat.floor_lt (by positivity : 0 ≤ X / (4 * A))).mp hlo
  · exact (Nat.le_floor_iff (by positivity : 0 ≤ 2 * X / A)).mp hhi

theorem product_budget (X A : ℝ) (hX : 0 ≤ X) (hA : 0 < A) :
    ((divisorCutoff A * upperCutoff X A : ℕ) : ℝ) ≤ 4 * X := by
  have hD : (divisorCutoff A : ℝ) ≤ 2 * A :=
    Nat.floor_le (by positivity : 0 ≤ 2 * A)
  have hU : (upperCutoff X A : ℝ) ≤ 2 * X / A :=
    Nat.floor_le (by positivity : 0 ≤ 2 * X / A)
  have hmul := mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg (upperCutoff X A))
  have hupper := (le_div_iff₀ hA).mp hU
  rw [Nat.cast_mul]
  nlinarith

theorem product_support_bounds (X A : ℝ) (s : Finset ℕ)
    (hX : 0 ≤ X) (hA : 0 < A)
    (hs : ∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 2 * A)
    (n : ℕ) (hn : n ∈ productSupport s (cofactors X A)) :
    0 < n ∧ (n : ℝ) ≤ 4 * X := by
  have hd := fun d hd => divisor_bounds A d hA (hs d hd)
  have hp : 0 < n := productSupport_positive s (cofactors X A)
    (fun d hd' => (hd d hd').1)
    (fun k hk => (cofactor_bounds X A hX hA k hk).1) n hn
  have hn' := productSupport_le s (cofactors X A) (divisorCutoff A)
    (upperCutoff X A) (fun d hd' => (hd d hd').2)
    (fun k hk => (Finset.mem_Ioc.mp hk).2) n hn
  exact ⟨hp, (by exact_mod_cast hn' : (n : ℝ) ≤
    (divisorCutoff A * upperCutoff X A : ℕ)).trans (product_budget X A hX hA)⟩

theorem count_identity (X A x δ : ℝ) (s : Finset ℕ) (weight : ℕ → ℝ)
    (hX : 0 < X) (hA : 0 < A)
    (hs : ∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 2 * A)
    (hx : x ∈ Icc X (2 * X)) (hδ : δ ∈ Icc 0 (1 / 2)) :
    divisorCount s weight (x - x * δ) x =
      SmoothedCountBoundary.sharp (productSupport s (cofactors X A))
        (coefficient s (cofactors X A) weight) x -
      SmoothedCountBoundary.sharp (productSupport s (cofactors X A))
        (coefficient s (cofactors X A) weight) (x - x * δ) := by
  have hw := window_bounds X x δ hX hx hδ
  have hf := fun d hd => floor_coverage X A x δ d hX hA (hs d hd) hx hδ
  exact divisorCount_eq_sharp s weight (lowerCutoff X A) (upperCutoff X A)
    (x - x * δ) x (fun d hd => (divisor_bounds A d hA (hs d hd)).1)
    (by linarith) hw.2 (fun d hd => (hf d hd).1) (fun d hd => (hf d hd).2)

theorem cutoffs_ready (X A : ℝ) (hX : 4 ≤ X) (hA : 1 ≤ A)
    (hscale : 8 * A ≤ X) :
    1 ≤ divisorCutoff A ∧ 1 ≤ lowerCutoff X A ∧ 1 ≤ upperCutoff X A ∧
      ((divisorCutoff A * upperCutoff X A : ℕ) : ℝ) ≤ X ^ (2 : ℕ) := by
  have hAp : 0 < A := by linarith
  have hlo := lowerCutoff_positive X A hAp (by linarith)
  have hD : 1 ≤ divisorCutoff A :=
    (Nat.le_floor_iff (by linarith : 0 ≤ 2 * A)).mpr (by norm_num; linarith)
  refine ⟨hD, hlo, hlo.trans (cutoff_order X A (by linarith) hAp), ?_⟩
  exact (product_budget X A (by linarith) hAp).trans (by nlinarith)

theorem eventually_scale (e : ℝ) (he : 0 < e) :
    ∀ᶠ X : ℝ in atTop, 4 ≤ X ∧
      ∀ A : ℝ, 1 ≤ A → A ≤ X ^ (1 - e) → 8 * A ≤ X := by
  filter_upwards [PolynomialLogEnvelope.eventually_constant_bound 8 e
    (by norm_num) he, eventually_ge_atTop (4 : ℝ)] with X hpower hX
  refine ⟨hX, ?_⟩
  intro A hA hAX
  have hXp : 0 < X := by linarith
  calc
    8 * A ≤ 8 * X ^ (1 - e) := mul_le_mul_of_nonneg_left hAX (by norm_num)
    _ ≤ X ^ e * X ^ (1 - e) :=
      mul_le_mul_of_nonneg_right hpower.2 (by positivity)
    _ = X := by rw [← Real.rpow_add hXp]; norm_num

/-- The original signed weights, not grouped weights, are the remaining input. -/
theorem eventual_approximation (e : ℝ) (he : 0 < e) :
    ∀ᶠ X : ℝ in atTop, 4 ≤ X ∧
      ∀ (A : ℝ) (s : Finset ℕ) (weight : ℕ → ℝ) (x δ : ℝ),
        1 ≤ A → A ≤ X ^ (1 - e) →
        (∀ d ∈ s, A < (d : ℝ) ∧ (d : ℝ) ≤ 2 * A) →
        (∀ d ∈ s, |weight d| ≤ X ^ (1 / 1600 : ℝ)) →
        x ∈ Icc X (2 * X) → δ ∈ Icc 0 (1 / 2) →
        1 ≤ lowerCutoff X A ∧ 1 ≤ upperCutoff X A ∧
          ‖HarmanDivisorContour.error s weight (lowerCutoff X A) (upperCutoff X A)
            (X ^ (-19 / 20 : ℝ)) (-X) X (1 + 1 / Real.log X) δ x‖ ≤
              4 * X ^ (2 / 25 : ℝ) := by
  filter_upwards [HarmanDivisorContour.eventual_approximation,
    eventually_scale e he] with X hc hsX
  refine ⟨hsX.1, ?_⟩
  intro A s weight x δ hA hAX hs hw hx hδ
  have hXp : 0 < X := by linarith [hsX.1]
  have hAp : 0 < A := by linarith
  have hr := cutoffs_ready X A hsX.1 hA (hsX.2 A hA hAX)
  have hf := fun d hd => floor_coverage X A x δ d hXp hAp (hs d hd) hx hδ
  refine ⟨hr.2.1, hr.2.2.1, ?_⟩
  exact hc.2 s weight (divisorCutoff A) (lowerCutoff X A) (upperCutoff X A) x δ
    hr.1 hr.2.2.1 hr.2.2.2 (fun d hd => divisor_bounds A d hAp (hs d hd))
    hw hx hδ (fun d hd => (hf d hd).1) (fun d hd => (hf d hd).2)

end DyadicDivisorWindow

#print axioms DyadicDivisorWindow.count_identity
#print axioms DyadicDivisorWindow.eventual_approximation
run_cmd do
  for target in [``DyadicDivisorWindow.floor_coverage,
      ``DyadicDivisorWindow.lowerCutoff_scale,
      ``DyadicDivisorWindow.cofactor_bounds,
      ``DyadicDivisorWindow.product_support_bounds,
      ``DyadicDivisorWindow.count_identity,
      ``DyadicDivisorWindow.eventual_approximation] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "DYADIC DIVISOR WINDOW PASSED"
