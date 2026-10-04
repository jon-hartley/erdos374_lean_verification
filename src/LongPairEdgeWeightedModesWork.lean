import LongPairEdgeComplexMeanWork
import ShortSingletonWeightedModes

set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
universe u
namespace LongPairEdgeWeightedModesWork
open ShortSingletonComplex ShortSingletonWeightedModes
/-- The factor supports and their dyadic scales may vary independently with
the mode. This permits a joint Fourier-mode and dyadic-block index. -/
theorem eventually_bound_varying :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
      ∀ (ι : Type u) (I : Finset ι) (M N : ι → ℕ) (sm sn : ι → Finset ℕ)
        (coeff : ι → ℂ) (a b : ι → ℕ → ℂ) (T : ℝ),
        let Y : ℝ := X ^ (101 / 1000 : ℝ) / 2
        0 < T →
        (∀ i ∈ I, 1 ≤ M i) → (∀ i ∈ I, 1 ≤ N i) →
        (∀ i ∈ I, X ^ (1/2:ℝ) ≤ ((M i*N i:ℕ):ℝ)) →
        (∀ i ∈ I, ((M i*N i:ℕ):ℝ) ≤ X ^ (772/1000:ℝ)) →
        (∀ i ∈ I, X ^ (1/5:ℝ) ≤ (N i:ℝ)) →
        (∀ i ∈ I, (N i:ℝ) ≤ X ^ (229/1000:ℝ)) →
        (∀ i ∈ I, ∀ n ∈ sm i, M i < n ∧ n ≤ 2 * M i) →
        (∀ i ∈ I, ∀ n ∈ sn i, N i < n ∧ n ≤ 2 * N i) →
        (∀ i ∈ I, ∀ n ∈ sm i, ‖a i n‖ ≤ T) →
        (∀ i ∈ I, ∀ n ∈ sn i, ‖b i n‖ ≤ 1) →
        (1 / X) * (∫ x in Icc X (2 * X),
          (∑ i ∈ I, coeff i * productSum (sm i) (sn i) (a i) (b i)
            (x - x * (Y / X)) x).re ^ 2) ≤
          4 * T ^ 2 * (∑ i ∈ I, ‖coeff i‖) ^ 2 * Y ^ 2 * X ^ (-c) := by
  obtain ⟨c, hc, hmean⟩ := LongPairEdgeComplexMeanWork.eventually_bound
  refine ⟨c, hc, ?_⟩
  filter_upwards [hmean, eventually_ge_atTop (1 : ℝ)] with X hm hX
  refine ⟨hm.1, ?_⟩
  intro ι I M N sm sn coeff a b T
  dsimp only
  intro hT hM hN hAlow hAupper hNlow hNhigh hsm hsn ha hb
  let Y : ℝ := X ^ (101 / 1000 : ℝ) / 2
  let aa : ι → ℕ → ℂ := fun i n => scalarPhase (coeff i) * a i n
  let f : ι → ℝ → ℝ := fun i x =>
    (productSum (sm i) (sn i) (aa i) (b i) (x - x * (Y / X)) x).re
  have hXp : 0 < X := by linarith
  have hY : 0 ≤ Y := by positivity
  have hYX : Y ≤ X := by
    have hp : X ^ (101 / 1000 : ℝ) ≤ X := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (101 / 1000 : ℝ) ≤ 1)
    dsimp [Y]
    linarith
  have haa : ∀ i ∈ I, ∀ n ∈ sm i, ‖aa i n‖ ≤ T := by
    intro i hi n hn
    dsimp [aa]
    rw [norm_mul]
    calc
      _ ≤ 1 * T := mul_le_mul (scalarPhase_norm_le_one (coeff i)) (ha i hi n hn)
        (norm_nonneg _) (by norm_num)
      _ = T := one_mul _
  have hmeans : ∀ i ∈ I, (1 / X) * (∫ x in Icc X (2 * X), f i x ^ 2) ≤
      4 * T ^ 2 * Y ^ 2 * X ^ (-c) := by
    intro i hi
    exact hm.2 (M i) (N i) (sm i) (sn i) (aa i) (b i) T hT (hM i hi) (hN i hi) (hAlow i hi) (hAupper i hi) (hNlow i hi) (hNhigh i hi)
      (hsm i hi) (hsn i hi) (haa i hi) (hb i hi)
  have hf : ∀ i ∈ I, IntegrableOn (f i) (Icc X (2 * X)) :=
    fun i _ => productSum_re_integrable (sm i) (sn i) (aa i) (b i) X Y
  have hf2 : ∀ i ∈ I, IntegrableOn (fun x => f i x ^ 2) (Icc X (2 * X)) :=
    fun i _ => productSum_re_square_integrable (sm i) (sn i) (aa i) (b i) X Y hXp hY hYX
  have hpoint (x : ℝ) :
      (∑ i ∈ I, coeff i * productSum (sm i) (sn i) (a i) (b i)
        (x - x * (Y / X)) x).re = ∑ i ∈ I, ‖coeff i‖ * f i x := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact scalar_product_re (sm i) (sn i) (a i) (b i) (coeff i) _ _
  have hagg := ShortSingletonAggregation.normalized_mean_square I (fun i => ‖coeff i‖)
    f X (4 * T ^ 2 * Y ^ 2 * X ^ (-c)) hXp hf hf2 hmeans
  have hw : (∑ i ∈ I, |‖coeff i‖|) ^ 2 * (4 * T ^ 2 * Y ^ 2 * X ^ (-c)) =
      4 * T ^ 2 * (∑ i ∈ I, ‖coeff i‖) ^ 2 * Y ^ 2 * X ^ (-c) := by
    simp only [abs_of_nonneg (norm_nonneg _)]
    ring
  have heq :
      (fun x : ℝ =>
        (∑ i ∈ I, coeff i * productSum (sm i) (sn i) (a i) (b i)
          (x - x * (Y / X)) x).re ^ 2) =
      (fun x => (∑ i ∈ I, ‖coeff i‖ * f i x) ^ 2) := by
    funext x
    exact congrArg (fun t : ℝ => t ^ 2) (hpoint x)
  calc
    _ = (1 / X) * (∫ x in Icc X (2 * X), (∑ i ∈ I, ‖coeff i‖ * f i x) ^ 2) :=
      congrArg (fun g : ℝ → ℝ => (1 / X) * (∫ x in Icc X (2 * X), g x)) heq
    _ ≤ _ := hagg.trans_eq hw

#print axioms eventually_bound_varying
run_cmd do
  for decl in [``eventually_bound_varying] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXTENDED HARMAN EDGE COMPLEX MODE AGGREGATION PASSED"
end LongPairEdgeWeightedModesWork
