import HarmanDivisorWindow

/-!
Measurability and compact square integrability of the actual signed
floor-count remainder. These facts justify later integral comparisons
even though the counting function has jumps.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace SignedDivisorRegularity
open HarmanDivisorWindow

theorem measurable_floor_quotient (d : ℕ) :
    Measurable (fun x : ℝ => (⌊x / d⌋₊ : ℝ)) := by
  have hm : Monotone (fun x : ℝ => (⌊x / d⌋₊ : ℝ)) := by
    intro x y hxy
    change (⌊x / d⌋₊ : ℝ) ≤ (⌊y / d⌋₊ : ℝ)
    exact_mod_cast Nat.floor_mono (div_le_div_of_nonneg_right hxy (Nat.cast_nonneg d))
  exact hm.measurable

theorem measurable_count (s : Finset ℕ) (weight : ℕ → ℝ) (δ : ℝ) :
    Measurable (fun x : ℝ => divisorCount s weight (x - x * δ) x) := by
  unfold divisorCount
  apply Finset.measurable_fun_sum
  intro d hd
  exact ((measurable_floor_quotient d).sub
    ((measurable_floor_quotient d).comp (by fun_prop))).const_mul _

theorem measurable_remainder (s : Finset ℕ) (weight : ℕ → ℝ) (δ : ℝ) :
    Measurable (fun x : ℝ => remainder s weight (x - x * δ) x) := by
  unfold remainder
  exact (measurable_count s weight δ).sub (by fun_prop)

theorem count_bound (s : Finset ℕ) (weight : ℕ → ℝ) (X x δ : ℝ)
    (hX : 0 ≤ X) (hx : x ∈ Icc X (2 * X)) (hδ : δ ∈ Icc 0 1) :
    |divisorCount s weight (x - x * δ) x| ≤
      ∑ d ∈ s, |weight d| * (⌊(2 * X) / d⌋₊ : ℝ) := by
  unfold divisorCount
  calc
    _ ≤ ∑ d ∈ s, |weight d * ((⌊x / d⌋₊ : ℝ) - (⌊(x - x * δ) / d⌋₊ : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro d hd
      have hxp : 0 ≤ x := hX.trans hx.1
      have hleft : x - x * δ ≤ x := by nlinarith [hδ.1]
      have hfloor : (⌊(x - x * δ) / d⌋₊ : ℝ) ≤ (⌊x / d⌋₊ : ℝ) := by
        exact_mod_cast Nat.floor_mono
          (div_le_div_of_nonneg_right hleft (Nat.cast_nonneg d))
      have hupper : (⌊x / d⌋₊ : ℝ) ≤ (⌊(2 * X) / d⌋₊ : ℝ) := by
        exact_mod_cast Nat.floor_mono
          (div_le_div_of_nonneg_right hx.2 (Nat.cast_nonneg d))
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤
        (⌊x / d⌋₊ : ℝ) - (⌊(x - x * δ) / d⌋₊ : ℝ))]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      linarith [show (0 : ℝ) ≤ (⌊(x - x * δ) / d⌋₊ : ℝ) by positivity]

theorem remainder_bound (s : Finset ℕ) (weight : ℕ → ℝ) (X x δ : ℝ)
    (hX : 0 ≤ X) (hx : x ∈ Icc X (2 * X)) (hδ : δ ∈ Icc 0 1) :
    |remainder s weight (x - x * δ) x| ≤
      (∑ d ∈ s, |weight d| * (⌊(2 * X) / d⌋₊ : ℝ)) +
        (2 * X * δ) * |reciprocalMass s weight| := by
  have hxp : 0 ≤ x := hX.trans hx.1
  unfold remainder
  calc
    _ ≤ |divisorCount s weight (x - x * δ) x| +
        |(x - (x - x * δ)) * reciprocalMass s weight| := abs_sub _ _
    _ ≤ (∑ d ∈ s, |weight d| * (⌊(2 * X) / d⌋₊ : ℝ)) +
        (2 * X * δ) * |reciprocalMass s weight| := by
      apply add_le_add (count_bound s weight X x δ hX hx hδ)
      rw [show x - (x - x * δ) = x * δ by ring, abs_mul,
        abs_of_nonneg (mul_nonneg hxp hδ.1)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hx.2 hδ.1) (abs_nonneg _)

theorem integrable_remainder_square (s : Finset ℕ) (weight : ℕ → ℝ) (X δ : ℝ)
    (hX : 0 ≤ X) (hδ : δ ∈ Icc 0 1) :
    IntegrableOn (fun x : ℝ => (remainder s weight (x - x * δ) x) ^ 2)
      (Icc X (2 * X)) := by
  let B := (∑ d ∈ s, |weight d| * (⌊(2 * X) / d⌋₊ : ℝ)) +
    (2 * X * δ) * |reciprocalMass s weight|
  apply Measure.integrableOn_of_bounded isCompact_Icc.measure_lt_top.ne
    ((measurable_remainder s weight δ).pow_const 2).aestronglyMeasurable (M := B ^ 2)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hh := pow_le_pow_left₀ (abs_nonneg _)
    (remainder_bound s weight X x δ hX hx hδ) 2
  simpa only [sq_abs] using hh

end SignedDivisorRegularity

#print axioms SignedDivisorRegularity.integrable_remainder_square
run_cmd do
  for target in [``SignedDivisorRegularity.measurable_count,
      ``SignedDivisorRegularity.measurable_remainder,
      ``SignedDivisorRegularity.count_bound,
      ``SignedDivisorRegularity.remainder_bound,
      ``SignedDivisorRegularity.integrable_remainder_square] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "SIGNED DIVISOR REGULARITY PASSED"
