import ShortSingletonMasks
import ShortSingletonCollection
import ShortSingletonComplex

/-! Exact collection after the two Fourier masks. Endpoints may depend on the
original prime or on the physical first factor; no representations are lost. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter
open scoped BigOperators

namespace ShortSingletonMaskedCollection
open ShortSingletonMasks ShortSingletonCollection ShortSingletonComplex
open UpperAfter545Remaining (floorKernel)

def modeWeight (Q : ℕ) (t : Mode Q) (w : ℕ × ℕ → ℂ)
    (lo hi cut : ℕ → ℕ) (a : ℕ × ℕ) : ℂ :=
  w a * leftPhase Q t (lo a.1) (hi a.1) * highPhase Q t (cut (index a))

def modeCoefficient (S : Finset (ℕ × ℕ)) (Q : ℕ) (t : Mode Q)
    (w : ℕ × ℕ → ℂ) (lo hi cut : ℕ → ℕ) : ℕ → ℂ :=
  coefficient S (modeWeight Q t w lo hi cut)

def maskedSum (S : Finset (ℕ × ℕ)) (B : Finset ℕ) (w : ℕ × ℕ → ℂ)
    (lo hi cut : ℕ → ℕ) (L R : ℝ) : ℂ :=
  ∑ a ∈ S, ∑ q ∈ B, w a *
    ((prefixIndicator (hi a.1) q - prefixIndicator (lo a.1) q) *
      (1-prefixIndicator (cut (index a)) q)) * (floorKernel L R (index a*q) : ℂ)

theorem modeWeight_norm_le (S : Finset (ℕ × ℕ)) (Q : ℕ) (t : Mode Q)
    (w : ℕ × ℕ → ℂ) (lo hi cut : ℕ → ℕ) (hw : ∀ a ∈ S, ‖w a‖ ≤ 1) :
    ∀ a ∈ S, ‖modeWeight Q t w lo hi cut a‖ ≤ 1 := by
  intro a ha
  simp only [modeWeight, norm_mul, highPhase_norm, mul_one]
  exact (mul_le_mul (hw a ha) (leftPhase_norm_le Q t _ _)
    (norm_nonneg _) (by norm_num)).trans (by norm_num)

theorem modeCoefficient_norm_le (S : Finset (ℕ × ℕ)) (Q : ℕ) (t : Mode Q)
    (w : ℕ × ℕ → ℂ) (lo hi cut : ℕ → ℕ) (n : ℕ) (hn : n ≠ 0)
    (hw : ∀ a ∈ S, ‖w a‖ ≤ 1) :
    ‖modeCoefficient S Q t w lo hi cut n‖ ≤ (n.divisors.card : ℝ) :=
  coefficient_norm_le S _ n hn (modeWeight_norm_le S Q t w lo hi cut hw)

theorem productSum_collected (S : Finset (ℕ × ℕ)) (B : Finset ℕ)
    (Q : ℕ) (t : Mode Q) (w : ℕ × ℕ → ℂ) (lo hi cut : ℕ → ℕ) (L R : ℝ) :
    productSum (support S) B (modeCoefficient S Q t w lo hi cut)
      (rightPhase Q t) L R =
      ∑ a ∈ S, ∑ q ∈ B, modeWeight Q t w lo hi cut a *
        rightPhase Q t q * (floorKernel L R (index a*q) : ℂ) := by
  unfold productSum modeCoefficient
  simp_rw [mul_assoc, ←Finset.mul_sum]
  rw [grouped_sum]

theorem maskedSum_expansion (S : Finset (ℕ × ℕ)) (B : Finset ℕ)
    (Q : ℕ) (w : ℕ × ℕ → ℂ) (lo hi cut : ℕ → ℕ) (L R : ℝ)
    (hB : ∀ q ∈ B, q ≤ Q) :
    maskedSum S B w lo hi cut L R =
      ∑ t : Mode Q, scalar Q t * productSum (support S) B
        (modeCoefficient S Q t w lo hi cut) (rightPhase Q t) L R := by
  unfold maskedSum
  calc
    _ = ∑ a ∈ S, ∑ q ∈ B, ∑ t : Mode Q,
        scalar Q t * (modeWeight Q t w lo hi cut a * rightPhase Q t q *
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

theorem dependent_maskedSum (P : Finset ℕ) (D : ℕ → Finset ℕ) (B : Finset ℕ)
    (w : ℕ × ℕ → ℂ) (lo hi cut : ℕ → ℕ) (L R : ℝ) :
    maskedSum (representations P D) B w lo hi cut L R =
      ∑ p ∈ P, ∑ d ∈ D p, ∑ q ∈ B, w (p,d) *
        ((prefixIndicator (hi p) q-prefixIndicator (lo p) q)*
          (1-prefixIndicator (cut (p*d)) q)) * (floorKernel L R (p*d*q) : ℂ) := by
  unfold maskedSum
  rw [representation_sum]
  rfl

theorem eventual_modeCoefficient_cap (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      ∀ (S : Finset (ℕ × ℕ)) (Q : ℕ) (t : Mode Q) (w : ℕ × ℕ → ℂ)
        (lo hi cut : ℕ → ℕ) (n : ℕ),
        0 < n → (n : ℝ) ≤ X^2 → (∀ a ∈ S, ‖w a‖ ≤ 1) →
        ‖modeCoefficient S Q t w lo hi cut n‖ ≤ X^δ := by
  filter_upwards [eventual_coefficient_cap δ hδ] with X hX
  refine ⟨hX.1, ?_⟩
  intro S Q t w lo hi cut n hn hnX hw
  exact hX.2 S _ n hn hnX (modeWeight_norm_le S Q t w lo hi cut hw)

run_cmd do
  for decl in [``modeWeight_norm_le, ``modeCoefficient_norm_le, ``productSum_collected,
      ``maskedSum_expansion, ``dependent_maskedSum, ``eventual_modeCoefficient_cap] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "EXACT MASKED PRIME-DIVISOR COLLECTION AND UNIFORM PHASE CAPS PASSED"

end ShortSingletonMaskedCollection
