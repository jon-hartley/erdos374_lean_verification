import ProductExpressionEnvelope
import NormalizedDyadicCap
import FlatPowerCap

/-!
Saving for the actual mixed product at every moment order in a fixed
interval separated from two. The flat factor supplies the full-product
cap. The moment order and all lengths are chosen after one common cutoff.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace VariableMixedSaving
open Erdos374.HarmanGram152 ProductMomentExpression

theorem range_from_length (X Q T η p : ℝ) (hX : 1 ≤ X) (hT : 1 ≤ T)
    (hp : 2 ≤ p) (hQ : X ^ η * T ^ (4 / (p + 2)) ≤ Q) :
    X ^ η ≤ Q ∧ T ^ (4 : ℕ) * (X ^ η) ^ (p + 2) ≤ Q ^ (p + 2) := by
  have hXp : 0 < X := by linarith
  have hTp : 0 < T := by linarith
  have hden : 0 < p + 2 := by linarith
  have hTpow : 1 ≤ T ^ (4 / (p + 2)) := Real.one_le_rpow hT (by positivity)
  refine ⟨(le_mul_of_one_le_right (by positivity) hTpow).trans hQ, ?_⟩
  have hh := Real.rpow_le_rpow (by positivity : 0 ≤ X ^ η * T ^ (4 / (p + 2)))
    hQ hden.le
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hTp.le] at hh
  have hexp : 4 / (p + 2) * (p + 2) = 4 := by field_simp
  rw [hexp] at hh
  norm_cast at hh
  simpa only [mul_comm] using hh

theorem eventually_bound (ell η ρ s : ℝ)
    (hell : 0 < ell) (hη : 0 < η) (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
        ∀ (K lo hi M : ℕ) (support : Finset ℕ) (coeff : ℕ → ℂ) (a T σ p : ℝ),
          X ^ ell ≤ (K : ℝ) → (K : ℝ) ≤ X → K ≤ lo → hi ≤ 2 * K →
          1 ≤ M → (M : ℝ) ≤ X → 2 + s ≤ p → p ≤ 3 →
          X ^ η * T ^ (4 / (p + 2)) ≤ (K * M : ℕ) →
          1 ≤ T → T ≤ X → 1 ≤ σ →
          (∀ n ∈ support, M < n ∧ n ≤ 2 * M) →
          (∑ n ∈ support, ‖coeff n‖ ^ 2) ≤ X ^ ε * M →
          (∀ t ∈ Icc a (a + T), X ^ ρ ≤ |t| ∧ |t| ≤ X) →
          (∫ t in Icc a (a + T),
            ‖verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t *
              verticalDirichlet152 support coeff σ t‖ ^ p) ≤ X ^ (-c) := by
  obtain ⟨k, hk, hkη, hflat⟩ := FlatPowerCap.eventually_bound ell ρ η hell hρ hρone hη
  let θ := k * s / 8
  let ε := θ / 1000
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hθη : θ ≤ η * s / 8 := by dsimp [θ]; gcongr
  have hθk : θ ≤ k / 8 := by
    have hh := mul_le_of_le_one_right hk.le hs1
    dsimp [θ]
    linarith
  have hεk : ε ≤ k := by dsimp [ε]; linarith
  have hmargin : 3 * (2 * ε + ε) < θ / 10 := by dsimp [ε]; linarith
  obtain ⟨D, hD, C, hC, hmoment⟩ := ProductMomentExpression.integral_bound ε hε
  refine ⟨θ / 4, by positivity, ε, hε, ?_⟩
  filter_upwards [hflat,
    ProductExpressionEnvelope.eventually_saving_bound D C ε ε η s θ
      hD hC hε.le hε.le hη hs hs1 hθ hθη hmargin,
    PolynomialLogEnvelope.eventually_constant_bound 26 (θ / 4)
      (by norm_num) (by positivity)] with X hf he hc
  refine ⟨hf.1, ?_⟩
  intro K lo hi M support coeff a T σ p hKlow hKX hlo hhi hM hMX hp hp3
    hlength hT hTX hσ hsupport henergy htimes
  have hXp : 0 < X := by linarith [hf.1]
  have hTp : 0 < T := by linarith
  have hK : 1 ≤ K := by
    exact_mod_cast (Real.one_le_rpow hf.1 hell.le).trans hKlow
  have hQ : 1 ≤ K * M := by nlinarith
  have hQX : (K * M : ℕ) ≤ X ^ 2 := by
    have hh := mul_le_mul hKX hMX (Nat.cast_nonneg M) hXp.le
    simpa only [Nat.cast_mul, pow_two] using hh
  have hsk : ∀ n ∈ Finset.Ioc lo hi, K < n ∧ n ≤ 2 * K := by
    intro n hn
    have hh := Finset.mem_Ioc.mp hn
    omega
  have hek : (∑ n ∈ Finset.Ioc lo hi, ‖(1 : ℂ)‖ ^ 2) ≤ X ^ (0 : ℝ) * K := by
    simp only [Real.rpow_zero, norm_one, one_pow, Finset.sum_const,
      nsmul_eq_mul, mul_one, Nat.card_Ioc, one_mul]
    exact_mod_cast (show hi - lo ≤ K by omega)
  have hcap : ∀ t ∈ Icc a (a + T),
      ‖verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t *
        verticalDirichlet152 support coeff σ t‖ ≤ X ^ (-k / 2) := by
    intro t ht
    rw [norm_mul]
    calc
      _ ≤ X ^ (-k) * X ^ (ε / 2) :=
        mul_le_mul
          (hf.2 K lo hi hKlow hKX hlo hhi t σ (htimes t ht).1 (htimes t ht).2 hσ)
          (NormalizedDyadicCap.norm_le_rpow support M coeff σ t X ε
            hM hσ hXp hsupport henergy) (norm_nonneg _) (by positivity)
      _ = X ^ (-k + ε / 2) := by rw [← Real.rpow_add hXp]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hf.1 (by linarith)
  have hpower : (X ^ (-k / 2)) ^ (p - 2) ≤ X ^ (-θ) := by
    rw [← Real.rpow_mul hXp.le]
    apply Real.rpow_le_rpow_of_exponent_le hf.1
    have hh := mul_le_mul_of_nonneg_left (show s ≤ p - 2 by linarith) hk.le
    dsimp [θ]
    nlinarith [mul_pos hk hs]
  have hh := hmoment K M (Finset.Ioc lo hi) support (fun _ => 1) coeff
    a T 0 ε X σ (X ^ (-k / 2)) p (X ^ (-θ)) hK hM hTp hXp hσ
    (by positivity) (by linarith) (by linarith) (by positivity)
    hsk hsupport hek henergy hcap hpower
  rw [zero_add] at hh
  have hrange := range_from_length X (K * M : ℕ) T η p hf.1 hT (by linarith) hlength
  calc
    _ ≤ upperBound D C (K * M) T ε ε X (X ^ (-k / 2)) p (X ^ (-θ)) := hh
    _ ≤ 26 * X ^ (-θ / 2) := he.2 (K * M) T (X ^ (-k / 2)) p hQ hQX hT hTX
      hp hp3 hrange.1 hrange.2
      (Real.rpow_le_one_of_one_le_of_nonpos hf.1 (by linarith))
    _ ≤ X ^ (θ / 4) * X ^ (-θ / 2) :=
      mul_le_mul_of_nonneg_right hc.2 (by positivity)
    _ = X ^ (-(θ / 4)) := by rw [← Real.rpow_add hXp]; congr 1; ring

end VariableMixedSaving

#print axioms VariableMixedSaving.eventually_bound
run_cmd do
  for target in [``VariableMixedSaving.range_from_length,
      ``VariableMixedSaving.eventually_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "VARIABLE MIXED SAVING PASSED"
