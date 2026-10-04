import ShortSingletonComplexMean

/-! Finite complex-mode aggregation with the square of the sum of scalar
norms. The eventual threshold and saving are uniform in the index type,
finite mode set, coefficient functions, and positive left cap. -/

set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
universe u

namespace ShortSingletonWeightedModes
open ShortSingletonComplex

/-- Zero is normalized to zero; all other inputs have unit modulus. -/
def scalarPhase (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

theorem scalarPhase_norm_le_one (z : ℂ) : ‖scalarPhase z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [scalarPhase, hz]
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    simp [scalarPhase, hn]

theorem scalarPhase_recover (z : ℂ) : (‖z‖ : ℂ) * scalarPhase z = z := by
  by_cases hz : z = 0
  · simp [scalarPhase, hz]
  · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
    change (‖z‖ : ℂ) * (z / (‖z‖ : ℂ)) = z
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hn]

theorem productSum_mul_left (A B : Finset ℕ) (a b : ℕ → ℂ) (z : ℂ) (L R : ℝ) :
    productSum A B (fun n => z * a n) b L R = z * productSum A B a b L R := by
  simp only [productSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem scalar_product_re (A B : Finset ℕ) (a b : ℕ → ℂ) (z : ℂ) (L R : ℝ) :
    (z * productSum A B a b L R).re =
      ‖z‖ * (productSum A B (fun n => scalarPhase z * a n) b L R).re := by
  have he : z * productSum A B a b L R =
      (‖z‖ : ℂ) * productSum A B (fun n => scalarPhase z * a n) b L R := by
    rw [productSum_mul_left, ← mul_assoc, scalarPhase_recover]
  rw [he]
  simp

def realCoefficient (A B : Finset ℕ) (a b : ℕ → ℂ) (n : ℕ) : ℝ :=
  FactoredDivisorWeights.coefficient A B (fun m => (a m).re) (fun m => (b m).re) n -
    FactoredDivisorWeights.coefficient A B (fun m => (a m).im) (fun m => (b m).im) n

theorem productSum_re_remainder (A B : Finset ℕ) (a b : ℕ → ℂ) (L R : ℝ) :
    (productSum A B a b L R).re =
      HarmanDivisorWindow.remainder (FactoredDivisorWeights.support A B)
        (realCoefficient A B a b) L R := by
  simp only [productSum_re, realRemainder, HarmanDivisorWindow.remainder_eq_sum,
    realCoefficient, sub_mul, Finset.sum_sub_distrib]

theorem productSum_re_integrable (A B : Finset ℕ) (a b : ℕ → ℂ) (X Y : ℝ) :
    IntegrableOn (fun x => (productSum A B a b (x - x * (Y / X)) x).re)
      (Icc X (2 * X)) := by
  have he : (fun x : ℝ => (productSum A B a b (x - x * (Y / X)) x).re) =
      (fun x => HarmanDivisorWindow.remainder (FactoredDivisorWeights.support A B)
        (realCoefficient A B a b) (x - x * (Y / X)) x) := by
    funext x
    exact productSum_re_remainder A B a b _ _
  rw [he]
  simpa only [div_eq_mul_inv, mul_assoc] using
    TailRemainderBand.moving_remainder_integrable (FactoredDivisorWeights.support A B)
      (realCoefficient A B a b) X Y

theorem productSum_re_square_integrable (A B : Finset ℕ) (a b : ℕ → ℂ)
    (X Y : ℝ) (hX : 0 < X) (hY : 0 ≤ Y) (hYX : Y ≤ X) :
    IntegrableOn (fun x => (productSum A B a b (x - x * (Y / X)) x).re ^ 2)
      (Icc X (2 * X)) := by
  have he : (fun x : ℝ => (productSum A B a b (x - x * (Y / X)) x).re ^ 2) =
      (fun x => HarmanDivisorWindow.remainder (FactoredDivisorWeights.support A B)
        (realCoefficient A B a b) (x - x * (Y / X)) x ^ 2) := by
    funext x
    exact congrArg (fun t : ℝ => t ^ 2) (productSum_re_remainder A B a b _ _)
  rw [he]
  exact SignedDivisorRegularity.integrable_remainder_square
    (FactoredDivisorWeights.support A B) (realCoefficient A B a b) X (Y / X)
    hX.le ⟨div_nonneg hY hX.le, (div_le_one hX).mpr hYX⟩

/-- There is no loss depending on the number of modes. In particular the
same saving and threshold work for any finite index type and mode set. -/
theorem eventually_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
      ∀ (ι : Type u) (I : Finset ι) (M N : ℕ) (sm sn : Finset ℕ)
        (coeff : ι → ℂ) (a b : ι → ℕ → ℂ) (T : ℝ),
        let A : ℝ := (M * N : ℕ)
        let Y : ℝ := X ^ (101 / 1000 : ℝ) / 2
        0 < T → 1 ≤ M → 1 ≤ N →
        X ^ (59 / 200 : ℝ) ≤ A → A ≤ X ^ (731 / 1000 : ℝ) →
        X ^ (39 / 1000 : ℝ) ≤ (N : ℝ) → (N : ℝ) ≤ X ^ (8 / 35 : ℝ) →
        (∀ n ∈ sm, M < n ∧ n ≤ 2 * M) →
        (∀ n ∈ sn, N < n ∧ n ≤ 2 * N) →
        (∀ i ∈ I, ∀ n ∈ sm, ‖a i n‖ ≤ T) →
        (∀ i ∈ I, ∀ n ∈ sn, ‖b i n‖ ≤ 1) →
        (1 / X) * (∫ x in Icc X (2 * X),
          (∑ i ∈ I, coeff i * productSum sm sn (a i) (b i)
            (x - x * (Y / X)) x).re ^ 2) ≤
          4 * T ^ 2 * (∑ i ∈ I, ‖coeff i‖) ^ 2 * Y ^ 2 * X ^ (-c) := by
  obtain ⟨c, hc, hmean⟩ := ShortSingletonComplexMean.eventually_bound
  refine ⟨c, hc, ?_⟩
  filter_upwards [hmean, eventually_ge_atTop (1 : ℝ)] with X hm hX
  refine ⟨hm.1, ?_⟩
  intro ι I M N sm sn coeff a b T
  dsimp only
  intro hT hM hN hAlow hAupper hNlow hNupper hsm hsn ha hb
  let Y : ℝ := X ^ (101 / 1000 : ℝ) / 2
  let aa : ι → ℕ → ℂ := fun i n => scalarPhase (coeff i) * a i n
  let f : ι → ℝ → ℝ := fun i x =>
    (productSum sm sn (aa i) (b i) (x - x * (Y / X)) x).re
  have hXp : 0 < X := by linarith
  have hY : 0 ≤ Y := by positivity
  have hYX : Y ≤ X := by
    have hp : X ^ (101 / 1000 : ℝ) ≤ X := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (101 / 1000 : ℝ) ≤ 1)
    dsimp [Y]
    linarith
  have haa : ∀ i ∈ I, ∀ n ∈ sm, ‖aa i n‖ ≤ T := by
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
    exact hm.2 M N sm sn (aa i) (b i) T hT hM hN hAlow hAupper hNlow hNupper
      hsm hsn (haa i hi) (hb i hi)
  have hf : ∀ i ∈ I, IntegrableOn (f i) (Icc X (2 * X)) :=
    fun i _ => productSum_re_integrable sm sn (aa i) (b i) X Y
  have hf2 : ∀ i ∈ I, IntegrableOn (fun x => f i x ^ 2) (Icc X (2 * X)) :=
    fun i _ => productSum_re_square_integrable sm sn (aa i) (b i) X Y hXp hY hYX
  have hpoint (x : ℝ) :
      (∑ i ∈ I, coeff i * productSum sm sn (a i) (b i) (x - x * (Y / X)) x).re =
        ∑ i ∈ I, ‖coeff i‖ * f i x := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact scalar_product_re sm sn (a i) (b i) (coeff i) _ _
  have hagg := ShortSingletonAggregation.normalized_mean_square I (fun i => ‖coeff i‖)
    f X (4 * T ^ 2 * Y ^ 2 * X ^ (-c)) hXp hf hf2 hmeans
  have hw : (∑ i ∈ I, |‖coeff i‖|) ^ 2 * (4 * T ^ 2 * Y ^ 2 * X ^ (-c)) =
      4 * T ^ 2 * (∑ i ∈ I, ‖coeff i‖) ^ 2 * Y ^ 2 * X ^ (-c) := by
    simp only [abs_of_nonneg (norm_nonneg _)]
    ring
  have heq :
      (fun x : ℝ =>
        (∑ i ∈ I, coeff i * productSum sm sn (a i) (b i)
          (x - x * (Y / X)) x).re ^ 2) =
      (fun x => (∑ i ∈ I, ‖coeff i‖ * f i x) ^ 2) := by
    funext x
    exact congrArg (fun t : ℝ => t ^ 2) (hpoint x)
  calc
    _ = (1 / X) * (∫ x in Icc X (2 * X), (∑ i ∈ I, ‖coeff i‖ * f i x) ^ 2) :=
      congrArg (fun g : ℝ → ℝ => (1 / X) * (∫ x in Icc X (2 * X), g x)) heq
    _ ≤ _ := hagg.trans_eq hw

/-- The factor supports and their dyadic scales may vary independently with
the mode. This permits a joint Fourier-mode and dyadic-block index. -/
theorem eventually_bound_varying :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
      ∀ (ι : Type u) (I : Finset ι) (M N : ι → ℕ) (sm sn : ι → Finset ℕ)
        (coeff : ι → ℂ) (a b : ι → ℕ → ℂ) (T : ℝ),
        let Y : ℝ := X ^ (101 / 1000 : ℝ) / 2
        0 < T →
        (∀ i ∈ I, 1 ≤ M i) → (∀ i ∈ I, 1 ≤ N i) →
        (∀ i ∈ I, X ^ (59 / 200 : ℝ) ≤ ((M i * N i : ℕ) : ℝ)) →
        (∀ i ∈ I, ((M i * N i : ℕ) : ℝ) ≤ X ^ (731 / 1000 : ℝ)) →
        (∀ i ∈ I, X ^ (39 / 1000 : ℝ) ≤ (N i : ℝ)) →
        (∀ i ∈ I, (N i : ℝ) ≤ X ^ (8 / 35 : ℝ)) →
        (∀ i ∈ I, ∀ n ∈ sm i, M i < n ∧ n ≤ 2 * M i) →
        (∀ i ∈ I, ∀ n ∈ sn i, N i < n ∧ n ≤ 2 * N i) →
        (∀ i ∈ I, ∀ n ∈ sm i, ‖a i n‖ ≤ T) →
        (∀ i ∈ I, ∀ n ∈ sn i, ‖b i n‖ ≤ 1) →
        (1 / X) * (∫ x in Icc X (2 * X),
          (∑ i ∈ I, coeff i * productSum (sm i) (sn i) (a i) (b i)
            (x - x * (Y / X)) x).re ^ 2) ≤
          4 * T ^ 2 * (∑ i ∈ I, ‖coeff i‖) ^ 2 * Y ^ 2 * X ^ (-c) := by
  obtain ⟨c, hc, hmean⟩ := ShortSingletonComplexMean.eventually_bound
  refine ⟨c, hc, ?_⟩
  filter_upwards [hmean, eventually_ge_atTop (1 : ℝ)] with X hm hX
  refine ⟨hm.1, ?_⟩
  intro ι I M N sm sn coeff a b T
  dsimp only
  intro hT hM hN hAlow hAupper hNlow hNupper hsm hsn ha hb
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
    exact hm.2 (M i) (N i) (sm i) (sn i) (aa i) (b i) T hT (hM i hi) (hN i hi)
      (hAlow i hi) (hAupper i hi) (hNlow i hi) (hNupper i hi)
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

#print axioms eventually_bound
#print axioms eventually_bound_varying
run_cmd do
  for decl in [``scalarPhase_norm_le_one, ``scalarPhase_recover, ``productSum_mul_left,
      ``scalar_product_re, ``productSum_re_remainder, ``productSum_re_integrable,
      ``productSum_re_square_integrable, ``eventually_bound, ``eventually_bound_varying] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "UNIFORM COMPLEX MODE AGGREGATION WITH ABSOLUTE-COEFFICIENT LOSS PASSED"

end ShortSingletonWeightedModes
