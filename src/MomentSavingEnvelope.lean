import MomentLengthRatio

/-!
Uniform saving in the mixed-product moment expression. The moment order
can vary in a fixed interval separated from two. The length margin and
the complete coefficient bounds are explicit hypotheses.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section

namespace MomentSavingEnvelope
open MomentLengthRatio

theorem ratio_bounds (p s : ℝ) (hs : 0 < s)
    (hp : 2 + s ≤ p) (hp3 : p ≤ 3) :
    s / 4 ≤ ratioExponent p ∧ ratioExponent p ≤ 1 / 3 := by
  have hd : 0 < 6 - p := by linarith
  constructor
  · apply (le_div_iff₀ hd).mpr
    have hh : 0 ≤ s * (p - 2) := mul_nonneg hs.le (by linarith)
    nlinarith
  · unfold ratioExponent
    apply (div_le_iff₀ hd).mpr
    linarith

theorem bound (X η s θ Q T p A B V J : ℝ)
    (hX : 1 ≤ X) (hη : 0 < η) (hs : 0 < s) (hs1 : s ≤ 1)
    (hθ : 0 < θ) (hθη : θ ≤ η * s / 8)
    (hQ : X ^ η ≤ Q) (hT : 0 < T)
    (hp : 2 + s ≤ p) (hp3 : p ≤ 3)
    (hlength : T ^ (4 : ℕ) * (X ^ η) ^ (p + 2) ≤ Q ^ (p + 2))
    (hA : 0 ≤ A) (hB : 0 < B) (hV : 0 ≤ V) (_hJ : 0 ≤ J)
    (hAbound : A ≤ X ^ (θ / 10))
    (hBbound : B ≤ X ^ (θ / 10) * T / Q ^ 2)
    (hVbound : V ≤ X ^ (θ / 10) * (1 + T / Q))
    (hJbound : J ≤ X ^ (θ / 10)) :
    (B / X ^ (-θ)) ^ ratioExponent p * V +
      J * (2 : ℝ) ^ p * (A * (2 : ℝ) ^ (p - 2) + 1) * X ^ (-θ) ≤
        26 * X ^ (-θ / 2) := by
  have hXp : 0 < X := by linarith
  have hZ : 1 ≤ X ^ η := Real.one_le_rpow hX hη.le
  have hQp : 0 < Q := by linarith
  have hp2 : 2 < p := by linarith
  have hr := ratio_bounds p s hs hp hp3
  have hr0 : 0 ≤ ratioExponent p := by linarith [hr.1]
  have hratio := MomentLengthRatio.bound Q T (X ^ η) p hZ hQ hT hp2
    (by linarith) hlength
  have hbase : B / X ^ (-θ) ≤
      X ^ (θ / 10 + θ) * (T / Q ^ 2) := by
    calc
      _ ≤ (X ^ (θ / 10) * T / Q ^ 2) / X ^ (-θ) :=
        div_le_div_of_nonneg_right hBbound (by positivity)
      _ = (X ^ (θ / 10) / X ^ (-θ)) * (T / Q ^ 2) := by ring
      _ = _ := by rw [← Real.rpow_sub hXp]; congr 2; ring
  have hexponent : (θ / 10 + θ) * ratioExponent p + θ / 10 -
      η * (2 * ratioExponent p) ≤ -θ := by
    have hsη : η * s ≤ η := mul_le_of_le_one_right hη.le hs1
    have hθη' : θ / 10 + θ ≤ η := by linarith
    have hh := mul_le_mul_of_nonneg_right hθη' hr0
    have hh' := mul_le_mul_of_nonneg_left hr.1 hη.le
    nlinarith
  have hfirst : (B / X ^ (-θ)) ^ ratioExponent p * V ≤
      2 * X ^ (-θ / 2) := by
    calc
      _ ≤ (X ^ (θ / 10 + θ) * (T / Q ^ 2)) ^ ratioExponent p *
          (X ^ (θ / 10) * (1 + T / Q)) := by gcongr
      _ = X ^ ((θ / 10 + θ) * ratioExponent p + θ / 10) *
          ((T / Q ^ 2) ^ ratioExponent p * (1 + T / Q)) := by
        rw [Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_mul hXp.le, Real.rpow_add hXp]
        ring
      _ ≤ X ^ ((θ / 10 + θ) * ratioExponent p + θ / 10) *
          (2 / (X ^ η) ^ (2 * ratioExponent p)) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = 2 * X ^ ((θ / 10 + θ) * ratioExponent p + θ / 10 -
          η * (2 * ratioExponent p)) := by
        rw [← Real.rpow_mul hXp.le, Real.rpow_sub hXp]
        ring
      _ ≤ 2 * X ^ (-θ) := by gcongr
      _ ≤ _ := by
        gcongr
        linarith
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
  have hDone : 1 ≤ X ^ (θ / 10) := Real.one_le_rpow hX (by positivity)
  have hbracket : A * (2 : ℝ) ^ (p - 2) + 1 ≤ 3 * X ^ (θ / 10) := by
    have hh := mul_le_mul hAbound htwosmall (by positivity)
      (show 0 ≤ X ^ (θ / 10) by positivity)
    nlinarith
  have hsecond : J * (2 : ℝ) ^ p *
      (A * (2 : ℝ) ^ (p - 2) + 1) * X ^ (-θ) ≤
        24 * X ^ (-θ / 2) := by
    calc
      _ ≤ X ^ (θ / 10) * 8 * (3 * X ^ (θ / 10)) * X ^ (-θ) := by gcongr
      _ = 24 * X ^ (θ / 10 + θ / 10 - θ) := by
        rw [show θ / 10 + θ / 10 - θ = (θ / 10 + θ / 10) + -θ by ring,
          Real.rpow_add hXp, Real.rpow_add hXp]
        ring
      _ ≤ _ := by gcongr; linarith
  linarith

end MomentSavingEnvelope

#print axioms MomentSavingEnvelope.bound
run_cmd do
  for target in [``MomentSavingEnvelope.ratio_bounds,
      ``MomentSavingEnvelope.bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "MOMENT SAVING ENVELOPE PASSED"
