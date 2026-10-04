import LongPairEdgeHarmanMeanWork
import ShortSingletonComplex
import ShortSingletonAggregation

/-! The actual half-width mean-square estimate for real parts of complex
factored floor sums. Only the left coefficient cap T is paid, as 4*T^2.
All support representations and literal natural-floor discrepancies remain. -/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace LongPairEdgeComplexMeanWork
open ShortSingletonComplex

/-- Uniform complex factor coefficients, with an arbitrary positive left cap. -/
theorem eventually_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
      ∀ (M N : ℕ) (sm sn : Finset ℕ) (a b : ℕ → ℂ) (T : ℝ),
        let A : ℝ := (M * N : ℕ)
        let Y : ℝ := X ^ (101 / 1000 : ℝ) / 2
        0 < T →
        1 ≤ M → 1 ≤ N → X ^ (1/2:ℝ) ≤ A → A ≤ X ^ (772/1000:ℝ) →
        X ^ (1/5:ℝ) ≤ (N : ℝ) → (N : ℝ) ≤ X ^ (229/1000:ℝ) →
        (∀ n ∈ sm, M < n ∧ n ≤ 2 * M) →
        (∀ n ∈ sn, N < n ∧ n ≤ 2 * N) →
        (∀ n ∈ sm, ‖a n‖ ≤ T) → (∀ n ∈ sn, ‖b n‖ ≤ 1) →
        (1 / X) * (∫ x in Icc X (2 * X),
          (productSum sm sn a b (x - x * (Y / X)) x).re ^ 2) ≤
            4 * T ^ 2 * Y ^ 2 * X ^ (-c) := by
  obtain ⟨c, hc, hmean⟩ := LongPairEdgeHarmanMeanWork.eventually_bound
  refine ⟨c, hc, ?_⟩
  filter_upwards [hmean, eventually_ge_atTop (1 : ℝ)] with X hm hX
  refine ⟨hm.1, ?_⟩
  intro M N sm sn a b T
  dsimp only
  intro hT hM hN hAlow hAupper hNlow hNhigh hsm hsn ha hb
  let Y : ℝ := X ^ (101 / 1000 : ℝ) / 2
  let ar : ℕ → ℝ := fun n => (a n).re / T
  let ai : ℕ → ℝ := fun n => (a n).im / T
  let br : ℕ → ℝ := fun n => (b n).re
  let bi : ℕ → ℝ := fun n => (b n).im
  let left : Fin 2 → ℕ → ℝ := fun i => if i = 0 then ar else ai
  let right : Fin 2 → ℕ → ℝ := fun i => if i = 0 then br else bi
  let w : Fin 2 → ℝ := fun i => if i = 0 then T else -T
  let weights : Fin 2 → ℕ → ℝ := fun i =>
    FactoredDivisorWeights.coefficient sm sn (left i) (right i)
  have hXp : 0 < X := by linarith
  have hY : 0 ≤ Y := by positivity
  have hYX : Y ≤ X := by
    have hp : X ^ (101 / 1000 : ℝ) ≤ X := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (101 / 1000 : ℝ) ≤ 1)
    dsimp [Y]
    linarith
  obtain ⟨har, hai⟩ := normalized_parts_le_one sm a T hT ha
  have hbr : ∀ n ∈ sn, |br n| ≤ 1 :=
    fun n hn => (Complex.abs_re_le_norm (b n)).trans (hb n hn)
  have hbi : ∀ n ∈ sn, |bi n| ≤ 1 :=
    fun n hn => (Complex.abs_im_le_norm (b n)).trans (hb n hn)
  have hleft : ∀ i : Fin 2, ∀ n ∈ sm, |left i n| ≤ 1 := by
    intro i n hn
    dsimp [left]
    split_ifs
    · exact har n hn
    · exact hai n hn
  have hright : ∀ i : Fin 2, ∀ n ∈ sn, |right i n| ≤ 1 := by
    intro i n hn
    dsimp [right]
    split_ifs
    · exact hbr n hn
    · exact hbi n hn
  have hmeans (i : Fin 2) :
      (1 / X) * (∫ x in Icc X (2 * X),
        HarmanDivisorWindow.remainder (FactoredDivisorWeights.support sm sn)
          (weights i) (x - x * (Y / X)) x ^ 2) ≤ Y ^ 2 * X ^ (-c) :=
    hm.2 M N sm sn (left i) (right i) hM hN hAlow hAupper hNlow hNhigh
      hsm hsn (hleft i) (hright i)
  have hpoint (x : ℝ) : (productSum sm sn a b (x - x * (Y / X)) x).re =
      ∑ i : Fin 2, w i * HarmanDivisorWindow.remainder
        (FactoredDivisorWeights.support sm sn) (weights i)
        (x - x * (Y / X)) x := by
    rw [productSum_re,
      realRemainder_normalize_left sm sn (fun n => (a n).re) (fun n => (b n).re)
        T _ _ hT.ne',
      realRemainder_normalize_left sm sn (fun n => (a n).im) (fun n => (b n).im)
        T _ _ hT.ne']
    simp [Fin.sum_univ_two, w, weights, left, right, ar, ai, br, bi, realRemainder]
    ring
  have hagg := ShortSingletonAggregation.divisor_remainders
    (Finset.univ : Finset (Fin 2)) w
    (fun _ => FactoredDivisorWeights.support sm sn) weights X Y (Y ^ 2 * X ^ (-c))
    hXp hY hYX (fun i _ => hmeans i)
  have hw : (∑ i : Fin 2, |w i|) ^ 2 * (Y ^ 2 * X ^ (-c)) =
      4 * T ^ 2 * Y ^ 2 * X ^ (-c) := by
    norm_num [w, Fin.sum_univ_two, abs_of_pos hT]
    ring
  have heq : (fun x : ℝ => (productSum sm sn a b (x - x * (Y / X)) x).re ^ 2) =
      (fun x => (∑ i : Fin 2, w i * HarmanDivisorWindow.remainder
        (FactoredDivisorWeights.support sm sn) (weights i)
        (x - x * (Y / X)) x) ^ 2) := by
    funext x
    exact congrArg (fun t : ℝ => t ^ 2) (hpoint x)
  calc
    _ = (1 / X) * (∫ x in Icc X (2 * X),
        (∑ i : Fin 2, w i * HarmanDivisorWindow.remainder
          (FactoredDivisorWeights.support sm sn) (weights i)
          (x - x * (Y / X)) x) ^ 2) :=
      congrArg (fun f : ℝ → ℝ => (1 / X) * (∫ x in Icc X (2 * X), f x)) heq
    _ ≤ _ := hagg.trans_eq hw

#print axioms eventually_bound
run_cmd do
  for ax in (← Lean.collectAxioms ``eventually_bound) do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "EXTENDED HARMAN EDGE COMPLEX REAL-PART MEAN SQUARE PASSED"

end LongPairEdgeComplexMeanWork
