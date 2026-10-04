import MomentLengthRatio

/-!
Uniform algebraic growth for the MomentThreshold expression at moment
orders between two and three, including the even endpoint p = 2.
This follows the envelope proof in ProductMomentDecay.

The caller still supplies the supremum cap and its power condition when
applying MomentThreshold.integral_bound, and must bound the actual band
count by J. This algebraic theorem does not replace those hypotheses.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section

namespace MomentGrowthEnvelope
open MomentLengthRatio

theorem length_ratio_bound (Q T p : ℝ)
    (hQ : 1 ≤ Q) (hT : 0 < T) (hp : 2 ≤ p) (hp3 : p ≤ 3)
    (hlength : T ^ (4 : ℕ) ≤ Q ^ (p + 2)) :
    (T / Q ^ 2) ^ ratioExponent p * (1 + T / Q) ≤ 2 := by
  have hQpos : 0 < Q := by linarith
  rcases eq_or_lt_of_le hp with rfl | hpgt
  · have hTQ : T ≤ Q := by
      apply (pow_le_pow_iff_left₀ hT.le hQpos.le
        (by norm_num : (4 : ℕ) ≠ 0)).mp
      norm_num at hlength
      exact hlength
    have hdiv : T / Q ≤ 1 := (div_le_one hQpos).mpr hTQ
    simpa only [ratioExponent, sub_self, zero_div, Real.rpow_zero, one_mul]
      using (show 1 + T / Q ≤ 2 by linarith)
  · simpa only [Real.one_rpow, mul_one, div_one] using
      MomentLengthRatio.bound Q T 1 p (by norm_num) hQ hT hpgt
        (by linarith) (by simpa using hlength)

theorem bound (X δ Q T p A B V J : ℝ)
    (hX : 1 ≤ X) (hδ : 0 < δ) (hQ : 1 ≤ Q) (hT : 0 < T)
    (hp : 2 ≤ p) (hp3 : p ≤ 3)
    (hlength : T ^ (4 : ℕ) ≤ Q ^ (p + 2))
    (hA : 0 ≤ A) (hB : 0 < B) (hV : 0 ≤ V) (_hJ : 0 ≤ J)
    (hAbound : A ≤ X ^ δ)
    (hBbound : B ≤ X ^ δ * T / Q ^ 2)
    (hVbound : V ≤ X ^ δ * (1 + T / Q))
    (hJbound : J ≤ X ^ δ) :
    (B / X ^ δ) ^ ratioExponent p * V +
      J * (2 : ℝ) ^ p * (A * (2 : ℝ) ^ (p - 2) + 1) * X ^ δ ≤
        26 * X ^ (3 * δ) := by
  have hXpos : 0 < X := by linarith
  have hQpos : 0 < Q := by linarith
  have hDpos : 0 < X ^ δ := Real.rpow_pos_of_pos hXpos _
  have hDone : 1 ≤ X ^ δ := Real.one_le_rpow hX hδ.le
  have hr : 0 ≤ ratioExponent p := by
    unfold ratioExponent
    exact div_nonneg (by linarith) (by linarith)
  have hratio := length_ratio_bound Q T p hQ hT hp hp3 hlength
  have hbase : B / X ^ δ ≤ T / Q ^ 2 := by
    apply (div_le_div_of_nonneg_right hBbound hDpos.le).trans_eq
    field_simp
  have hfirst : (B / X ^ δ) ^ ratioExponent p * V ≤
      2 * X ^ (3 * δ) := by
    have hbpow := Real.rpow_le_rpow (div_nonneg hB.le hDpos.le) hbase hr
    calc
      _ ≤ (T / Q ^ 2) ^ ratioExponent p *
          (X ^ δ * (1 + T / Q)) :=
        mul_le_mul hbpow hVbound hV (by positivity)
      _ = X ^ δ * ((T / Q ^ 2) ^ ratioExponent p * (1 + T / Q)) := by
        ring
      _ ≤ X ^ δ * 2 := mul_le_mul_of_nonneg_left hratio hDpos.le
      _ ≤ _ := by
        have hh := Real.rpow_le_rpow_of_exponent_le hX
          (show δ ≤ 3 * δ by linarith)
        nlinarith
  have htwo : (2 : ℝ) ^ p ≤ 8 := by
    calc
      _ ≤ (2 : ℝ) ^ (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hp3
      _ = _ := by norm_num
  have htwosmall : (2 : ℝ) ^ (p - 2) ≤ 2 := by
    calc
      _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = _ := by norm_num
  have hbracket : A * (2 : ℝ) ^ (p - 2) + 1 ≤ 3 * X ^ δ := by
    have hh := mul_le_mul hAbound htwosmall
      (by positivity : 0 ≤ (2 : ℝ) ^ (p - 2)) hDpos.le
    nlinarith
  have hsecond : J * (2 : ℝ) ^ p *
      (A * (2 : ℝ) ^ (p - 2) + 1) * X ^ δ ≤ 24 * X ^ (3 * δ) := by
    calc
      _ ≤ X ^ δ * 8 * (3 * X ^ δ) * X ^ δ := by gcongr
      _ = _ := by
        rw [show 3 * δ = δ + δ + δ by ring,
          Real.rpow_add hXpos, Real.rpow_add hXpos]
        ring
  linarith

end MomentGrowthEnvelope

#print axioms MomentGrowthEnvelope.length_ratio_bound
#print axioms MomentGrowthEnvelope.bound
run_cmd do
  for target in [``MomentGrowthEnvelope.length_ratio_bound,
      ``MomentGrowthEnvelope.bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "MOMENT GROWTH ENVELOPE PASSED"
