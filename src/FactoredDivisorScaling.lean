import FactoredDivisorMeanSquare

/-!
Exact homogeneity of the signed factored remainder. Scaling each of two
factor weights by B scales its squared spatial mean by B^4.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter MeasureTheory Set

namespace FactoredDivisorScaling
open FactoredDivisorWeights HarmanDivisorWindow MellinCofactorCoverage

theorem coefficient_scale (sm sn : Finset ℕ) (am an : ℕ → ℝ)
    (a b : ℝ) (d : ℕ) :
    FactoredDivisorWeights.coefficient sm sn (fun n => a * am n)
      (fun n => b * an n) d =
        (a * b) * FactoredDivisorWeights.coefficient sm sn am an d := by
  unfold FactoredDivisorWeights.coefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pair hp
  ring

theorem remainder_scale (s : Finset ℕ) (weight : ℕ → ℝ) (a L R : ℝ) :
    remainder s (fun d => a * weight d) L R = a * remainder s weight L R := by
  unfold remainder divisorCount reciprocalMass
  simp_rw [mul_assoc, mul_div_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem factored_remainder_scale (sm sn : Finset ℕ) (am an : ℕ → ℝ)
    (a b L R : ℝ) :
    remainder (support sm sn)
      (FactoredDivisorWeights.coefficient sm sn (fun n => a * am n)
        (fun n => b * an n)) L R =
      (a * b) * remainder (support sm sn)
        (FactoredDivisorWeights.coefficient sm sn am an) L R := by
  have heq := funext (coefficient_scale sm sn am an a b)
  rw [heq, remainder_scale]

theorem normalized_remainder (sm sn : Finset ℕ) (am an : ℕ → ℝ)
    (B L R : ℝ) (hB : B ≠ 0) :
    remainder (support sm sn) (FactoredDivisorWeights.coefficient sm sn am an) L R =
      B ^ 2 * remainder (support sm sn)
        (FactoredDivisorWeights.coefficient sm sn
          (fun n => am n / B) (fun n => an n / B)) L R := by
  have hm : (fun n => B * (am n / B)) = am := by
    funext n
    field_simp
  have hn : (fun n => B * (an n / B)) = an := by
    funext n
    field_simp
  simpa only [hm, hn, pow_two] using factored_remainder_scale sm sn
    (fun n => am n / B) (fun n => an n / B) B B L R

theorem normalized_mean_square (sm sn : Finset ℕ) (am an : ℕ → ℝ)
    (B X δ : ℝ) (hB : B ≠ 0) :
    (1 / X) * (∫ x in Icc X (2 * X),
      remainder (support sm sn) (FactoredDivisorWeights.coefficient sm sn am an)
        (x - x * δ) x ^ 2) =
      B ^ 4 * ((1 / X) * (∫ x in Icc X (2 * X),
        remainder (support sm sn) (FactoredDivisorWeights.coefficient sm sn
          (fun n => am n / B) (fun n => an n / B)) (x - x * δ) x ^ 2)) := by
  simp_rw [normalized_remainder sm sn am an B _ _ hB, mul_pow, ← pow_mul]
  rw [integral_const_mul]
  norm_num
  ring

end FactoredDivisorScaling

#print axioms FactoredDivisorScaling.normalized_mean_square
run_cmd do
  for target in [``FactoredDivisorScaling.coefficient_scale,
      ``FactoredDivisorScaling.remainder_scale,
      ``FactoredDivisorScaling.factored_remainder_scale,
      ``FactoredDivisorScaling.normalized_remainder,
      ``FactoredDivisorScaling.normalized_mean_square] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "FACTORED DIVISOR SCALING PASSED"
