import LongerTupleCollection
import ShortSingletonMasks
import ShortSingletonComplex

/-! Two exact Fourier masks with arbitrary ordered representations.
The interval endpoints may depend on the entire representation, while the
physical cutoff depends on its product. All collisions remain in the
collected coefficient. No actual-family adapter is asserted here. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter
open scoped BigOperators

namespace LongerTupleMaskedCollection
open ShortSingletonMasks LongerTupleCollection ShortSingletonComplex
open UpperAfter545Remaining (floorKernel)

variable {α : Type*}

def modeWeight (index : α → ℕ) (Q : ℕ) (t : Mode Q) (w : α → ℂ)
    (lo hi : α → ℕ) (cut : ℕ → ℕ) (a : α) : ℂ :=
  w a * leftPhase Q t (lo a) (hi a) * highPhase Q t (cut (index a))

def modeCoefficient (S : Finset α) (index : α → ℕ) (Q : ℕ) (t : Mode Q)
    (w : α → ℂ) (lo hi : α → ℕ) (cut : ℕ → ℕ) : ℕ → ℂ :=
  coefficient S index (modeWeight index Q t w lo hi cut)

def maskedSum (S : Finset α) (index : α → ℕ) (B : Finset ℕ) (w : α → ℂ)
    (lo hi : α → ℕ) (cut : ℕ → ℕ) (L R : ℝ) : ℂ :=
  ∑ a ∈ S, ∑ q ∈ B, w a *
    ((prefixIndicator (hi a) q - prefixIndicator (lo a) q) *
      (1-prefixIndicator (cut (index a)) q)) * (floorKernel L R (index a*q) : ℂ)

theorem modeWeight_norm_le (S : Finset α) (index : α → ℕ)
    (Q : ℕ) (t : Mode Q) (w : α → ℂ) (lo hi : α → ℕ) (cut : ℕ → ℕ)
    (hw : ∀ a ∈ S, ‖w a‖ ≤ 1) :
    ∀ a ∈ S, ‖modeWeight index Q t w lo hi cut a‖ ≤ 1 := by
  intro a ha
  simp only [modeWeight, norm_mul, highPhase_norm, mul_one]
  exact (mul_le_mul (hw a ha) (leftPhase_norm_le Q t _ _)
    (norm_nonneg _) (by norm_num)).trans (by norm_num)

theorem modeCoefficient_norm_le (k : ℕ) (S : Finset α) (index : α → ℕ)
    (encode : α → Fin k → ℕ)
    (hprod : ∀ a ∈ S, index a = ∏ i, encode a i)
    (hinj : Set.InjOn encode (S : Set α))
    (Q : ℕ) (t : Mode Q) (w : α → ℂ) (lo hi : α → ℕ) (cut : ℕ → ℕ)
    (n : ℕ) (hn : n ≠ 0) (hw : ∀ a ∈ S, ‖w a‖ ≤ 1) :
    ‖modeCoefficient S index Q t w lo hi cut n‖ ≤ (n.divisors.card : ℝ)^k :=
  coefficient_norm_le k S index encode hprod hinj _
    (modeWeight_norm_le S index Q t w lo hi cut hw) n hn

theorem productSum_collected (S : Finset α) (index : α → ℕ) (B : Finset ℕ)
    (Q : ℕ) (t : Mode Q) (w : α → ℂ) (lo hi : α → ℕ) (cut : ℕ → ℕ) (L R : ℝ) :
    productSum (support S index) B (modeCoefficient S index Q t w lo hi cut)
      (rightPhase Q t) L R =
      ∑ a ∈ S, ∑ q ∈ B, modeWeight index Q t w lo hi cut a *
        rightPhase Q t q * (floorKernel L R (index a*q) : ℂ) := by
  unfold productSum modeCoefficient
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [grouped_sum]

theorem maskedSum_expansion (S : Finset α) (index : α → ℕ) (B : Finset ℕ)
    (Q : ℕ) (w : α → ℂ) (lo hi : α → ℕ) (cut : ℕ → ℕ) (L R : ℝ)
    (hB : ∀ q ∈ B, q ≤ Q) :
    maskedSum S index B w lo hi cut L R =
      ∑ t : Mode Q, scalar Q t * productSum (support S index) B
        (modeCoefficient S index Q t w lo hi cut) (rightPhase Q t) L R := by
  unfold maskedSum
  calc
    _ = ∑ a ∈ S, ∑ q ∈ B, ∑ t : Mode Q,
        scalar Q t * (modeWeight index Q t w lo hi cut a * rightPhase Q t q *
          (floorKernel L R (index a*q) : ℂ)) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro q hq
      rw [separation Q _ _ _ q (hB q hq), Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t _
      unfold modeWeight
      ring
    _ = _ := by
      simp_rw [Finset.sum_comm (s := B) (t := Finset.univ)]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      rw [productSum_collected, Finset.mul_sum]
      simp_rw [Finset.mul_sum]

theorem eventual_modeCoefficient_cap (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      ∀ (S : Finset α) (index : α → ℕ) (encode : α → Fin k → ℕ),
        (∀ a ∈ S, index a = ∏ i, encode a i) →
        Set.InjOn encode (S : Set α) →
        ∀ (Q : ℕ) (t : Mode Q) (w : α → ℂ) (lo hi : α → ℕ) (cut : ℕ → ℕ) (n : ℕ),
          0 < n → (n : ℝ) ≤ X^2 → (∀ a ∈ S, ‖w a‖ ≤ 1) →
          ‖modeCoefficient S index Q t w lo hi cut n‖ ≤ X^δ := by
  filter_upwards [eventually_divisor_power_cap k δ hδ] with X hX
  refine ⟨hX.1, ?_⟩
  intro S index encode hprod hinj Q t w lo hi cut n hn hnX hw
  exact (modeCoefficient_norm_le k S index encode hprod hinj Q t w lo hi cut n
    (by omega) hw).trans (hX.2 n hnX)

run_cmd do
  for decl in [``modeWeight_norm_le, ``modeCoefficient_norm_le, ``productSum_collected,
      ``maskedSum_expansion, ``eventual_modeCoefficient_cap] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXACT MASKED ORDERED REPRESENTATION COLLECTION PASSED"

end LongerTupleMaskedCollection
