import Item1ParameterCore

/-! Algebra for dividing a moment estimate by the averaging interval size. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace Item1ParameterMomentAlgebra

theorem normalize_moment {X A C E Q : ℝ} (p q r : ℕ) (hA : 0 < A)
    (hq : q + 2*r = p)
    (h : X^p ≤ A^q*A^q*(C*A^E)*(C*A^E)*Q) :
    (X/A^2)^p ≤ C^2*A^(2*E-4*(r:ℝ))*Q := by
  have hqr : (q:ℝ)+2*(r:ℝ) = (p:ℝ) := by exact_mod_cast hq
  have hpow : (A^q*A^q)*(A^E*A^E) = A^(2*E-4*(r:ℝ))*(A^2)^p := by
    calc
      (A^q*A^q)*(A^E*A^E) = A^((q:ℝ)+(q:ℝ)+E+E) := by
        rw [Real.rpow_add hA, Real.rpow_add hA, Real.rpow_add hA]
        simp only [Real.rpow_natCast]
        ring
      _ = A^((2*E-4*(r:ℝ))+(2*(p:ℝ))) := by
        congr 1
        linarith
      _ = A^(2*E-4*(r:ℝ))*(A^2)^p := by
        rw [Real.rpow_add hA]
        congr 1
        rw [show (2:ℝ)*(p:ℝ) = ((2*p:ℕ):ℝ) by push_cast; ring,
          Real.rpow_natCast, pow_mul]
  rw [div_pow]
  apply (div_le_iff₀ (pow_pos (pow_pos hA 2) p)).mpr
  calc
    X^p ≤ A^q*A^q*(C*A^E)*(C*A^E)*Q := h
    _ = C^2*((A^q*A^q)*(A^E*A^E))*Q := by ring
    _ = C^2*(A^(2*E-4*(r:ℝ))*(A^2)^p)*Q := by rw [hpow]
    _ = C^2*A^(2*E-4*(r:ℝ))*Q*(A^2)^p := by ring

end Item1ParameterMomentAlgebra

run_cmd do
  for ax in (← Lean.collectAxioms ``Item1ParameterMomentAlgebra.normalize_moment) do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in normalization"
  Lean.logInfo "PARAMETER MOMENT ALGEBRA: 1 standard-axiom theorem guard passed."
