import MertensPrimeInterval
import SieveGeometricGrid

/-! Actual prime reciprocal mass in a narrow logarithmic interval, and in
any frozen-prefix cubic strip. Closed lower endpoints are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
open Real

namespace SieveThinPrimeInterval

def delta (D s : ℝ) : ℝ := s^7/3 + 10/(s^2*log D)

theorem delta_nonneg (D s : ℝ) (hD : 1 < D) (hs : 0 < s) : 0 ≤ delta D s := by
  have hlD : 0 < log D := log_pos hD
  unfold delta
  positivity

theorem prime_interval_log_width (u a b W : ℝ) (S : Finset ℕ)
    (hu : 1 < u) (hua : u ≤ a) (hab : a ≤ b) (hW : 0 ≤ W)
    (hwidth : log b-log a ≤ W)
    (hS : ∀ p ∈ S, p.Prime ∧ a ≤ (p:ℝ) ∧ (p:ℝ) ≤ b) :
    ∑ p ∈ S, (p:ℝ)⁻¹ ≤ W/log u + 10/log u := by
  have ha : 1 < a := hu.trans_le hua
  have hla : 0 < log a := log_pos ha
  have hlu : 0 < log u := log_pos hu
  have hlb : 0 < log b := log_pos (ha.trans_le hab)
  have hluA : log u ≤ log a := log_le_log (by linarith) hua
  have hlog : log (log b/log a) ≤ W/log u := calc
    _ ≤ log b/log a-1 := log_le_sub_one_of_pos (div_pos hlb hla)
    _ = (log b-log a)/log a := by field_simp
    _ ≤ W/log a := div_le_div_of_nonneg_right hwidth hla.le
    _ ≤ W/log u := div_le_div_of_nonneg_left hW hlu hluA
  exact (MertensPrimeInterval.prime_reciprocal_interval a b S ha hab hS).trans
    (add_le_add hlog (div_le_div_of_nonneg_left (by norm_num) hlu hluA))

theorem prime_interval_bound (D s a b : ℝ) (S : Finset ℕ)
    (hD : 1 < D) (hs : 0 < s) (hua : D^(s^2) ≤ a) (hab : a ≤ b)
    (hwidth : log b-log a ≤ (s^9/3)*log D)
    (hS : ∀ p ∈ S, p.Prime ∧ a ≤ (p:ℝ) ∧ (p:ℝ) ≤ b) :
    ∑ p ∈ S, (p:ℝ)⁻¹ ≤ delta D s := by
  have hD0 : 0 < D := by linarith
  have hlD : 0 < log D := log_pos hD
  have hu : 1 < D^(s^2) := Real.one_lt_rpow hD (sq_pos_of_pos hs)
  have h := prime_interval_log_width (D^(s^2)) a b ((s^9/3)*log D) S
    hu hua hab (by positivity) hwidth hS
  have he : ((s^9/3)*log D)/log (D^(s^2))+10/log (D^(s^2)) = delta D s := by
    rw [Real.log_rpow hD0]
    unfold delta
    field_simp [hs.ne', hlD.ne']
  exact h.trans_eq he

/-- An arbitrary finite prime fiber in one cubic strip. Taking the actual
minimum and maximum avoids assuming that a clipped real interval is nonempty. -/
theorem cubic_strip_bound (D s A α β : ℝ) (S : Finset ℕ)
    (hD : 1 < D) (hs : 0 < s) (hA : 0 < A)
    (hwidth : β-α ≤ s^9)
    (hS : ∀ p ∈ S, p.Prime ∧ D^(s^2) ≤ (p:ℝ) ∧
      D^α ≤ A*(p:ℝ)^3 ∧ A*(p:ℝ)^3 < D^β) :
    ∑ p ∈ S, (p:ℝ)⁻¹ ≤ delta D s := by
  classical
  by_cases hne : S.Nonempty
  · let a : ℕ := S.min' hne
    let b : ℕ := S.max' hne
    have ha : a ∈ S := S.min'_mem hne
    have hb : b ∈ S := S.max'_mem hne
    have ha0 : 0 < (a:ℝ) := by exact_mod_cast (hS a ha).1.pos
    have hb0 : 0 < (b:ℝ) := by exact_mod_cast (hS b hb).1.pos
    have hD0 : 0 < D := by linarith
    have hlo := Real.log_le_log (Real.rpow_pos_of_pos hD0 α) (hS a ha).2.2.1
    have hhi := Real.log_lt_log (mul_pos hA (pow_pos hb0 3)) (hS b hb).2.2.2
    rw [Real.log_rpow hD0, Real.log_mul hA.ne' (pow_pos ha0 3).ne', Real.log_pow] at hlo
    rw [Real.log_rpow hD0, Real.log_mul hA.ne' (pow_pos hb0 3).ne', Real.log_pow] at hhi
    have hw := mul_le_mul_of_nonneg_right hwidth (log_pos hD).le
    apply prime_interval_bound D s a b S hD hs (hS a ha).2.1
    · exact_mod_cast S.min'_le b hb
    · norm_num at hlo hhi
      nlinarith
    · intro p hp
      exact ⟨(hS p hp).1, by exact_mod_cast S.min'_le p hp,
        by exact_mod_cast S.le_max' p hp⟩
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty, Finset.sum_empty]
    exact delta_nonneg D s hD hs

theorem outer_cubic_strip_bound (D s A : ℝ) (S : Finset ℕ)
    (hD : 1 < D) (hs : 0 < s) (hA : 0 < A)
    (hS : ∀ p ∈ S, p.Prime ∧ D^(s^2) ≤ (p:ℝ) ∧
      D ≤ A*(p:ℝ)^3 ∧ A*(p:ℝ)^3 < D^(SieveGeometricGrid.ratio s)) :
    ∑ p ∈ S, (p:ℝ)⁻¹ ≤ delta D s := by
  apply cubic_strip_bound D s A 1 (SieveGeometricGrid.ratio s) S hD hs hA
  · simp [SieveGeometricGrid.ratio]
  · simpa only [Real.rpow_one] using hS

theorem inner_cubic_strip_bound (D s A : ℝ) (S : Finset ℕ)
    (hD : 1 < D) (hs : 0 < s) (hA : 0 < A)
    (hS : ∀ p ∈ S, p.Prime ∧ D^(s^2) ≤ (p:ℝ) ∧
      D^(1/SieveGeometricGrid.ratio s) ≤ A*(p:ℝ)^3 ∧ A*(p:ℝ)^3 < D) :
    ∑ p ∈ S, (p:ℝ)⁻¹ ≤ delta D s := by
  apply cubic_strip_bound D s A (1/SieveGeometricGrid.ratio s) 1 S hD hs hA
  · have hx : 0 ≤ s^9 := by positivity
    have hq : 0 < 1+s^9 := by positivity
    unfold SieveGeometricGrid.ratio
    have hh : 1-1/(1+s^9) = s^9/(1+s^9) := by field_simp; ring
    rw [hh]
    exact (div_le_iff₀ hq).mpr (by nlinarith)
  · simpa only [Real.rpow_one] using hS

run_cmd do
  for decl in [``delta_nonneg, ``prime_interval_log_width, ``prime_interval_bound,
    ``cubic_strip_bound, ``outer_cubic_strip_bound, ``inner_cubic_strip_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL THIN PRIME INTERVAL AND CUBIC STRIP BOUNDS PASSED"
end SieveThinPrimeInterval
end
