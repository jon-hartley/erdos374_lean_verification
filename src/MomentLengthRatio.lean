import ProductMomentRatio

/-!
Real-order form of the length-ratio estimate. This generalizes the
fixed 5/2 calculation in ProductMomentRatio while keeping the positive
margin in the product length explicit.
-/

set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section

namespace MomentLengthRatio

def ratioExponent (p : ℝ) : ℝ := (p - 2) / (6 - p)

theorem product_identity (Q T p : ℝ) (hQ : 0 < Q) (hT : 0 < T)
    (hp6 : p < 6) :
    (T / Q ^ 2) ^ ratioExponent p * (T / Q) =
      (T ^ 4 / Q ^ (p + 2)) ^ (1 / (6 - p)) := by
  have hd : 6 - p ≠ 0 := ne_of_gt (by linarith)
  have he1 : ratioExponent p + 1 = 4 * (1 / (6 - p)) := by
    unfold ratioExponent
    field_simp
    ring
  have he2 : 2 * ratioExponent p + 1 = (p + 2) * (1 / (6 - p)) := by
    unfold ratioExponent
    field_simp
    ring
  rw [Real.div_rpow hT.le (sq_nonneg Q),
    Real.div_rpow (by positivity : 0 ≤ T ^ 4) (by positivity)]
  rw [← Real.rpow_natCast_mul hQ.le, ← Real.rpow_natCast_mul hT.le,
    ← Real.rpow_mul hQ.le]
  norm_num only [Nat.cast_ofNat]
  rw [← he1, ← he2, Real.rpow_add hT, Real.rpow_add hQ]
  simp only [Real.rpow_one]
  ring

theorem bound (Q T Z p : ℝ) (hZ : 1 ≤ Z) (hQZ : Z ≤ Q)
    (hT : 0 < T) (hp : 2 < p) (hp6 : p < 6)
    (hrange : T ^ 4 * Z ^ (p + 2) ≤ Q ^ (p + 2)) :
    (T / Q ^ 2) ^ ratioExponent p * (1 + T / Q) ≤
      2 / Z ^ (2 * ratioExponent p) := by
  have hZp : 0 < Z := by linarith
  have hQp : 0 < Q := by linarith
  have hd : 0 < 6 - p := by linarith
  have hr : 0 < ratioExponent p := div_pos (by linarith) hd
  have hfirst : T * Z ^ 2 ≤ Q ^ 2 := by
    have hpow : T ^ 4 * Z ^ (8 : ℕ) ≤ Q ^ (8 : ℕ) := by
      calc
        _ = (T ^ 4 * Z ^ (p + 2)) * Z ^ (6 - p) := by
          rw [mul_assoc, ← Real.rpow_add hZp]
          rw [show p + 2 + (6 - p) = (8 : ℝ) by ring]
          norm_num
        _ ≤ Q ^ (p + 2) * Q ^ (6 - p) :=
          mul_le_mul hrange (Real.rpow_le_rpow hZp.le hQZ hd.le)
            (by positivity) (by positivity)
        _ = _ := by
          rw [← Real.rpow_add hQp, show p + 2 + (6 - p) = (8 : ℝ) by ring]
          norm_num
    apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ T * Z ^ 2)
      (by positivity : 0 ≤ Q ^ 2) (by norm_num : (4 : ℕ) ≠ 0)).mp
    convert hpow using 1 <;> ring
  have hsmall : (T / Q ^ 2) ^ ratioExponent p ≤
      1 / Z ^ (2 * ratioExponent p) := by
    have hbase : T / Q ^ 2 ≤ 1 / Z ^ 2 :=
      (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hfirst)
    calc
      _ ≤ (1 / Z ^ 2) ^ ratioExponent p :=
        Real.rpow_le_rpow (by positivity) hbase hr.le
      _ = _ := by
        rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg Z),
          Real.one_rpow, ← Real.rpow_natCast_mul hZp.le]
        norm_num
  have hlarge : (T / Q ^ 2) ^ ratioExponent p * (T / Q) ≤
      1 / Z ^ (2 * ratioExponent p) := by
    rw [product_identity Q T p hQp hT hp6]
    have hbase : T ^ 4 / Q ^ (p + 2) ≤ 1 / Z ^ (p + 2) :=
      (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hrange)
    have hexp : 2 * ratioExponent p ≤ (p + 2) * (1 / (6 - p)) := by
      unfold ratioExponent
      calc
        _ = (2 * (p - 2)) / (6 - p) := by ring
        _ ≤ (p + 2) / (6 - p) :=
          div_le_div_of_nonneg_right (by linarith) hd.le
        _ = _ := by ring
    calc
      _ ≤ (1 / Z ^ (p + 2)) ^ (1 / (6 - p)) :=
        Real.rpow_le_rpow (by positivity) hbase (by positivity)
      _ = 1 / Z ^ ((p + 2) * (1 / (6 - p))) := by
        rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) (by positivity),
          Real.one_rpow, ← Real.rpow_mul hZp.le]
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (Real.rpow_le_rpow_of_exponent_le hZ hexp)
  calc
    _ = (T / Q ^ 2) ^ ratioExponent p +
        (T / Q ^ 2) ^ ratioExponent p * (T / Q) := by ring
    _ ≤ 1 / Z ^ (2 * ratioExponent p) + 1 / Z ^ (2 * ratioExponent p) :=
      add_le_add hsmall hlarge
    _ = _ := by ring

end MomentLengthRatio

#print axioms MomentLengthRatio.bound
run_cmd do
  for target in [``MomentLengthRatio.product_identity, ``MomentLengthRatio.bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "MOMENT LENGTH RATIO PASSED"
