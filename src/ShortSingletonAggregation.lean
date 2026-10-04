import FiniteDivisorFamily
import TailRemainderBand

/-! Weighted finite L2 aggregation. Its loss is the square of the absolute
coefficient sum, never the number of Fourier modes. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace ShortSingletonAggregation

theorem weighted_sum_square {ι : Type*} (S : Finset ι) (w f : ι → ℝ) :
    (∑ i ∈ S, w i * f i)^2 ≤
      (∑ i ∈ S, |w i|) * ∑ i ∈ S, |w i| * f i^2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
    (fun i _ => abs_nonneg (w i)) (fun i _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
  intro i _
  calc
    (w i*f i)^2 = (w i)^2*(f i)^2 := mul_pow _ _ _
    _ = |w i| *(|w i| *(f i)^2) := by rw [←sq_abs (w i)]; ring
    _ ≤ _ := le_rfl

theorem normalized_mean_square {ι : Type*} (S : Finset ι)
    (w : ι → ℝ) (f : ι → ℝ → ℝ) (X B : ℝ) (hX : 0 < X)
    (hf : ∀ i ∈ S, IntegrableOn (f i) (Icc X (2*X)))
    (hf2 : ∀ i ∈ S, IntegrableOn (fun x => f i x^2) (Icc X (2*X)))
    (hmean : ∀ i ∈ S, (1/X)*(∫ x in Icc X (2*X), f i x^2) ≤ B) :
    (1/X)*(∫ x in Icc X (2*X), (∑ i ∈ S, w i*f i x)^2) ≤
      (∑ i ∈ S, |w i|)^2 * B := by
  let C : ℝ := ∑ i ∈ S, |w i|
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => abs_nonneg (w i))
  have hsum : IntegrableOn (fun x => ∑ i ∈ S, w i*f i x) (Icc X (2*X)) := by
    have hh := integrable_finsetSum' S (fun i hi => (hf i hi).const_mul (w i))
    have he : (∑ i ∈ S, fun x => w i*f i x) = (fun x => ∑ i ∈ S, w i*f i x) := by
      funext x
      simp only [Finset.sum_apply]
    rw [he] at hh
    exact hh
  have hterms : ∀ i ∈ S, IntegrableOn (fun x => |w i| *f i x^2) (Icc X (2*X)) :=
    fun i hi => (hf2 i hi).const_mul |w i|
  have hmajor : IntegrableOn (fun x => C * ∑ i ∈ S, |w i| *f i x^2)
      (Icc X (2*X)) := by
    have hh : IntegrableOn (fun x => ∑ i ∈ S, |w i| *f i x^2) (Icc X (2*X)) := by
      have h := integrable_finsetSum' S hterms
      have he : (∑ i ∈ S, fun x => |w i| * f i x^2) =
          (fun x => ∑ i ∈ S, |w i| * f i x^2) := by
        funext x
        simp only [Finset.sum_apply]
      rw [he] at h
      exact h
    exact hh.const_mul C
  have hpoint (x : ℝ) : (∑ i ∈ S, w i*f i x)^2 ≤ C * ∑ i ∈ S, |w i| *f i x^2 :=
    weighted_sum_square S w (fun i => f i x)
  have hcombined : IntegrableOn (fun x => (∑ i ∈ S, w i*f i x)^2)
      (Icc X (2*X)) := by
    apply hmajor.mono' (hsum.aestronglyMeasurable.pow 2)
    exact Filter.Eventually.of_forall (fun x => by
      change ‖(∑ i ∈ S, w i*f i x)^2‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint x)
  calc
    _ ≤ (1/X)*(∫ x in Icc X (2*X), C * ∑ i ∈ S, |w i| *f i x^2) :=
      mul_le_mul_of_nonneg_left (integral_mono hcombined hmajor hpoint) (by positivity)
    _ = C * ∑ i ∈ S, |w i| *((1/X)*(∫ x in Icc X (2*X), f i x^2)) := by
      rw [integral_const_mul, integral_finsetSum S hterms]
      simp only [integral_const_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ C * ∑ i ∈ S, |w i| *B := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hmean i hi) (abs_nonneg _))
    _ = (∑ i ∈ S, |w i|)^2*B := by rw [←Finset.sum_mul]; dsimp [C]; ring

theorem divisor_remainders {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (supports : ι → Finset ℕ) (weights : ι → ℕ → ℝ)
    (X Y B : ℝ) (hX : 0 < X) (hY : 0 ≤ Y) (hYX : Y ≤ X)
    (hmean : ∀ i ∈ S, (1/X)*(∫ x in Icc X (2*X),
      HarmanDivisorWindow.remainder (supports i) (weights i) (x-x*(Y/X)) x ^2) ≤ B) :
    (1/X)*(∫ x in Icc X (2*X), (∑ i ∈ S, w i *
      HarmanDivisorWindow.remainder (supports i) (weights i) (x-x*(Y/X)) x)^2) ≤
        (∑ i ∈ S, |w i|)^2*B := by
  apply normalized_mean_square S w _ X B hX
  · intro i _
    simpa only [div_eq_mul_inv, mul_assoc] using
      TailRemainderBand.moving_remainder_integrable (supports i) (weights i) X Y
  · intro i _
    exact SignedDivisorRegularity.integrable_remainder_square (supports i) (weights i)
      X (Y/X) hX.le ⟨div_nonneg hY hX.le, (div_le_one hX).mpr hYX⟩
  · exact hmean

run_cmd do
  for decl in [``weighted_sum_square, ``normalized_mean_square, ``divisor_remainders] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "ABSOLUTE-COEFFICIENT L2 AGGREGATION PASSED"

end ShortSingletonAggregation
